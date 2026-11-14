# Track B — a genuine full-(B3) disagreement forces an UNMATCHABLE LIVE Kpt cut node
**14 November 2026. English-first proof / adversarial audit; stacked on combined PR #180.**

## Aim

Previously validated Track B cross-ambient theory proves a full corrected-(B3) failure in one finite Henson occurrence and passage in another, at a common source cut with aligned old ordinary-L prefixes, forces a **physical cut-adjacent original** in the failing occurrence whose complete next ordinary-L type is not permitted by the passing cut-star.

The integrated two-run PR #180 additionally constructs the exact exhaustive final index of ALL genuine Kpt nodes for each ACTUAL finite AlgorithmRun, plus the true per-cut Boolean source masks. Its physical live-node matching condition is logically equivalent to upper-L spectrum inclusion. We can now sharpen the disagreement into a **live Kpt source node that lacks any physically live match**, not merely a missing prescribed original label or an abstract type.

## Theorem A — one-sided actual live-index cover is impossible under B3 disagreement

Take two `P,Q : HensonRunCutData` with the SAME literal base E, numerical generation k and source coordinate cut c, but potentially different true seed sets, original pools, ambient truncation heights, actual parameter/meet closures and Kpt source-index sizes. Assume the true full corrected-(B3) test FAILS for P and PASSES for Q.

Let `paramsP,liveP,paramsQ,liveQ` be ANY exact physical active-node indexes for the two actual pre-cut closures at c (as produced by the verified true-run construction). In particular the projected indexed physical cut-star spectrum of P and Q equals their respective intrinsic `PhysicalCutStarUpperL` predicates for every complete next upper ordinary-L reduct.

Then **the directional physical live cover from P to Q is false**:
```
¬ IndexedCutStarLiveCover family nodeP liveP nodeQ liveQ c.
```

Proof: the same-base theorem supplies `SameInitialL P.ambient.L Q.ambient.L c`. Apply verified
`HensonCutOccurrence.failing_full_B3_has_unmatched_cutStar_original`
to the two TRUE run occurrences; obtain a genuinely selected, physically L-adjacent, cut-eligible original v of P and a complete next ordinary-L reduct
`R = (P.ambient.partialTypeAt(c+1)(P.original v)).lReduct`
**not permitted** by Q's cut-star profile. By verified
`star_name_complete_upperL_permitted`, this physical R IS permitted by P's cut-star. By PR #141's certified source-exhaustiveness and intrinsic spectrum theorem and the actual indexed projection equalities, this means `IndexedPhysicalCutStarUpperL Pidx c R` but `¬ IndexedPhysicalCutStarUpperL Qidx c R`.
If `IndexedCutStarLiveCover Pidx Qidx c` held, the verified one-sided inclusion theorem would send the actual live P-index witness of R to Q, a contradiction.

**No E expansion of a B3 continuation witness** is involved. The exact physical Kpt source was first constructed from the real AlgorithmRuns; this obstruction is about its true live node index.

## Theorem B — extract the unmatched TRUE live Kpt source node

Classically negate the explicit definition of `IndexedCutStarLiveCover`. This yields a true Kpt source index j of P, actual complete old and next `L^+` partial types T,U, satisfying
```
liveP c j = true,
kptFullOldAtCut(nodeP j)c = some(c,T),
kptFullUpperAtCut(nodeP j)c = some(c+1,U),
U.lReduct.binary (some (Fin.last c)) none 0 = true,
```
but with **no** live Kpt source index i of Q carrying a complete upper ordinary-L reduct equal to `U.lReduct` via a genuine old/upper Kpt ancestor pair.

The missing witness is therefore a REAL, active, cut-crossing, ordinary-L-cut-adjacent Kpt node in the FULL physical source, possibly a generated meet or auxiliary parameter. This is stronger than merely knowing that the selected macrodiary's active F-state differs. The converse of the live-name-cover theorem guarantees that the witness is an exact local cut-star *profile* obstruction, not an artifact of name-duplication or an arbitrary target representative.

## Theorem C — two actual finite runs have such a finite-index witness

Use the parent PR #180 theorem `two_runs_finite_indexed_cutStar_controls_full_B3` to CONSTRUCT separately exhaustive finite Kpt-node indexes for actual runs P,Q (and thus their projected spectrum exactness). Apply the preceding Theorem A/B. Conclude the existence of a finite true active Kpt node j in P with a positive physical cut edge and complete next-L type unmatched by any live cut-crossing Kpt node in Q whenever their full corrected B3 verdicts differ in the given direction.

This needs NO separate abstract `Full` predicate, hPool or old L-socle alignment hypothesis: these come from the verified true runs with shared E/k/c. The old **common source coordinate** and physical base E/k remain explicit real assumptions; deriving them across ALL occurrences of a canonical diary is still open.

## Hostile review (16)

1. `P` and `Q` are real AlgorithmRuns with original-prefix source seeds, not arbitrary Kpt sets or fabricated selected subpools.
2. Same base E/k and literal source cut c are explicit and are NOT implied by selected macrodiary F equivalence.
3. Full no-(I2) is required separately for each corrected-B3 prescribed source function; physical indexed relations exist even with I2 forks but cannot automatically supply B3 functions.
4. The true source uses Run.I(c+1) while the maintained finite name pool uses Run.I 0, and the finite indexed Kpt-node universe contains generated parameters and meets.
5. The old ordinary-L socle alignment comes from literal finite numerical-H construction and same E/k, not guessed from an abstract age-state.
6. The failing occurrence has the unmatched node; no symmetric conclusion is implied if failure/pass is reversed.
7. The physical cut adjacency is a positive ORDINARY-L atom of complete next upper L-reduct U, not auxiliary E.
8. Complete next ordinary-L reduct preservation includes all positive/negative directed bits, unary and diagonal data, not merely the cut edge.
9. The mismatch quantifies over TRUE live nodes and BOTH old/upper complete Kpt ancestor records. A terminal cut-level I1 node without crossing is not a false match.
10. The number of finite Kpt nodes in the two indexes may differ; the name relation is not a bijection or monoid orbit.
11. The missing node may be auxiliary q2 in the K4 cut-10 regression even when the selected x-only profile passes, and it must not be discarded.
12. No future–future edge of an arbitrary ordinary-L B3 continuation is copied from the ambient graph.
13. Empty cut-star in the failing occurrence is impossible under the actual Henson failure theorem; the proof extracts a physical cut-neighbour from its failed B3.
14. The result does NOT prove the proposed refined diary canonically determines the physical live cut-star; it supplies a precise necessary obstruction when the verdict changes.
15. The relative-fixed-source continuation/B3-loss equivalence, full I1/I2 event-dependent E record synchronization and labelled common inverse-source monoid orbit remain independent.
16. No unconditional exact Kk-free big Ramsey upper/lower degree or independent infinite diary unavoidability follows.

## Verification gate

Commit this English proof first. After PR #180's combined exact-head 646-report full Lean CI passes, formalize two or three named endpoints in `Kk/B3ActualRunMissingLiveNode.lean` and register exact source-axiom reports on a fresh/latest shared main, rather than stacking old central imports over concurrent A/C/D/E/F/G merges. Use full `lake build`, parser self-test, only standard `propext`, `Classical.choice`, `Quot.sound`, no sorryAx. Paper protected black prose remains untouched; global diary criterion stays pending.


## Post-merge checkpoint for formalization

The complete eight-endpoint two-run source package is now **verified and merged** as [PR #180](https://github.com/janhubicka/lean-kk/pull/180), exact-head full [CI 43613334917](https://github.com/janhubicka/lean-kk/actions/runs/43613334917): **646** named standard-only transitive axiom reports, no sorryAx, complete Lake build and parser self-test. This new independent branch is based on that merged source, not on the earlier nested audit-only branch. Three new public endpoints are planned, targeting **649** exact standard-only reports on the unchanged current main.

The first endpoint should expose BOTH a missing complete upper-L type R (indexed in the failing true run but absent from the passing true run) and the impossibility of a one-sided positive-cut live node cover. The second extracts a genuinely live Kpt node j with exact old and upper raw `L^+` ancestors and no matching active Q-node. The third derives existence of both finite Kpt indexes and the unmatched witness from TWO actual finite AlgorithmRuns alone (given failure/pass), without assuming artificial source completeness or preconstructed indexes. This remains a local necessary obstruction, not a global diary proof.
