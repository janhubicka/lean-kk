# Track E — genuine cross-height new-root novelty and bare-original source attribution

**14 November 2026. English proof and adversarial audit written before Lean.** Stacked on independently exact-head-verified but unmerged Track C [#196](https://github.com/janhubicka/lean-kk/pull/196) (head `9d34bf04c2a3f69306e7efd1f3064b7f0013b47f`), itself stacked on C #194/#192. Track E's true same-top seed monotonicity, full dependent-L+ physical crossing relation and extra-cut witness were merged into `main` in [PR #181](https://github.com/janhubicka/lean-kk/pull/181). Track E's actual same-top old-closure absorption is separately verified in [draft #197](https://github.com/janhubicka/lean-kk/pull/197); the present proof uses upstream Track C absorption directly and does not require any #197 source import.

## E44. The missing higher-top physical new-cut witness

Fix one actual normalized Kpt (S,M)-tree, genuine Kpt seed sets `X⊆Y`, and **two actual AlgorithmRuns**:

`R : AlgorithmRun H X oldTop`, `Q : AlgorithmRun H Y newTop`,

with `oldTop≤newTop`. Unlike the earlier same-top argument, require a **genuine old-top seed** `∃x∈X, lev x=oldTop`. Without it the old top may be a purely artificial topI marker; when a new run starts higher, it can skip that old top, so old selected-level containment fails.

Track C's verified `envelope_algorithmRun_selected_levels_mono_seed_height` gives
`R.I(i)⊆Q.I(i)` for **every** `i≤oldTop` (including the old top itself) by a real I1 witness at oldTop and downward actual I1/I2/I3 monotonicity.

Fix `cut<oldTop` and suppose `cut∈Q.I(cut)`, but `cut∉R.I(cut)`. Define the **actual** full pre-cut Kpt closures

`Zold = closure_(R.I(cut+1))(X)`,
`Znew = closure_(Q.I(cut+1))(Y)`.

Then **one of two genuine new physical witnesses exists**:

1. a Kpt node `z∈Znew\Zold` with `lev z=cut`; or
2. a complete old/upper **dependent L+** crossing pair `(T,U) ∈ Cross(Znew,cut) \ Cross(Zold,cut)`, including the full auxiliary E/negative-L old and upper type records.

### English proof

- `cut+1≤oldTop` gives `R.I(cut+1)⊆Q.I(cut+1)` by the genuine cross-height theorem. Together with literal `X⊆Y`, exact meet/parameter closure monotonicity gives `Zold⊆Znew` and inclusion of their entire physical crossing relations.
- If the old pre-cut closure were interesting at cut, `R.interesting_step` would force `cut∈R.I(cut)`, contrary to assumption. So the old cut is genuinely boring.
- If the new pre-cut closure were boring, `Q.noninteresting_step` gives `Q.I(cut)=Q.I(cut+1)`, whereas any selected element in the actual higher set has level `≥cut+1` by `Q.I_mem_bounds`; hence `cut∉Q.I(cut)`, contrary to assumption. So the new cut is genuinely interesting.
- The old source has no terminal node at cut (otherwise I1 interestingness). If the new source has one, it is literally absent from old source: the first alternative.
- Otherwise both terminal I1 flags are false. If there were no new full crossing pair, the two physical crossing relations would be equal, since old⊆new already. Track E's **kernel-checked genuine monoid theorem** `kpt_actual_interesting_iff_of_terminal_and_crossing_eq` would then identify their IsInterestingAt decisions, contradiction. Hence there exists a real new complete L+ crossing pair.

This is an actual **new-source witness** for a newly selected cut even with INCREASING numerical-H scan tops, and does not use a corrected-B3 converse or a selected graph-age shadow.

## E45. Attribute the extra cut to the *bare old and new physical ORIGINALS*

Now assume the new-run seeds have the corrected actual finite numerical-H+ form
`Y = closure_I(X) ∪ O`, where `O=(w↦finiteNumericH L k M.kptOriginal(w))''W` contains **only** genuine inserted Kpt originals—not all their ancestor prefixes.

At the tested `cut<oldTop≤newTop`, assume the inherited old parameter-generating levels satisfy

`I⊆R.I(cut+1)`.

This is **much weaker** than the earlier special case `I=R.I0` and `cut<every old selected q`. In particular one may take `I=R.I(cut+1)`, the true higher selected levels, for a *per-cut* statement.

Track C's cross-height theorem and literal `X⊆Y` yield
`I⊆Q.I(cut+1)`, even though the new run has a larger top. By the verified least-closure absorption theorem,

`closure_(Q.I(cut+1))(Y)=closure_(Q.I(cut+1))(X∪O)`.

Call that right-hand complete physical source `Zbare`.

Applying E44 to old and new actual runs and replacing the new source by its **literal equal** bare closure yields:

If `Q` selects an extra cut, there is either a **new terminal node** of `Zbare` or a **new full dependent L+ old/upper crossing pair** of `Zbare` absent from old pre-cut closure.

Therefore the physical obstruction comes from actual **old+new ORIGINAL nodes and their genuine parameter/meet closure**, not from the optional bookkeeping step of preinserting the old full closure. This remains valid at true I2 forks: the complete physical crossing relation is multivalued and retains all fake E bits. No B3 condition is assumed.

## E46. Cross-height finite-index specialization

If the actual taller numerical H+ run's corrected seed Y has a genuine original-prefix pool representation in the finite physical `finiteNumericH L k M`, Track C's verified exhaustive index constructor gives ONE finite `params : Finset (AdmissibleKptNode family)`, its exact live mask at every cut, and completeness for every true pre-cut closure.

At any extra selected cut below oldTop, choose its E44/E45 witness and use exact live-index coverage:
- new terminal node → ONE active index j of level cut and absent from the old source;
- new pair → ONE active index j whose **SAME** Kpt node has both `kptFullOldAtCut = some ⟨cut,T⟩` and `kptFullUpperAtCut = some ⟨cut+1,U⟩`, with that pair absent from the old canonical physical crossing relation.

No injective matching of two indexes is assumed; the new **index itself** is injected into the literal true final closure. The index size may depend on the physical numerical-H carrier and is not a uniform BRD bound.

## Adversarial checklist

1. **Old genuine top seed is essential.** A purely formal topI marker without a Kpt seed at oldTop may be skipped by the taller run, violating crossheight monotonicity.
2. **Only cuts STRICTLY BELOW oldTop.** The semantic step at oldTop itself can be compared via top-seed I1, but the old run has no interesting_step oldTop. A new cut in the strict interval `oldTop<cut<newTop` has no old run comparator.
3. **Literal same admissible Kpt tree.** Old and new sources must be nodes in ONE normalized dependent L+ source tree. Different generations/new raw-coordinate systems need genuine transport first; equal ordinary graph edges do not establish X⊆Y.
4. **The corrected new-root seed Y is ORIGINAL-only.** Reverting to the all-prefix new-root seed set forces every lower cut into I1 and destroys boundedness, as verified independently in Track C's negative regression.
5. **A new event need not be structural.** Extra cut may be a genuine monoid-level I3 non-skippability due to a new full E-dependent crossing pair; new terminal nodes alone do not capture it.
6. **No B3 converse.** The source test uses REAL Kpt monoid IsInterestingAt and full physical crossing relation; equality or failure of ordinary-L B3 age tests alone is insufficient.
7. **The old→new source inclusion is a theorem.** It uses actual selected-level inclusion at stage cut+1 and exact closure monotonicity in BOTH seed and level sets, not a claimed embedding of selected macrofront labels.
8. **Absorption needs I⊆old higher selected levels.** With I not selected above cut, preinserted old parameters may really cause extra I1/I2 events; do not discard that hypothesis.
9. **Per-cut I=R.I(cut+1) is not a global new-root schedule.** Each cut can define a different Y. To apply E45 at all cuts of one fixed Y, verify the higher-level containment separately at each cut.
10. **Same-node raw Options.** A complete crossing `(T,U)` is witnessed by ONE true Kpt node; do not combine T from one indexed original and U from another.
11. **The finite index is exact.** It must enumerate the full parameter-closed source, including auxiliary meets/fake E, not just selected real generator originals or graph-age shadows.
12. **No uniform finite carrier.** Each physical run is finite, but its parameter index can grow unboundedly with the ambient N and number of new roots.
13. **No source-label orbit.** Even equal selected-level skeletons and complete local crossing spectra do not determine the fully labelled dependent source; Track E's earlier meet-closed closure counterexample demonstrates this.
14. **Auxiliary K4 cuts 10/22 are genuine regression cases.** Such microlevels may be extra interesting and cannot be silently compressed into the macrodiary.
15. **No global BRD theorem.** The unbounded resolved-copy construction has not yet proved that every extra witness corresponds to a prescribed diary event, or constructed a common outgoing genuine monoid source copy.

## Exact Lean targets

- Cross-height actual two-run new terminal/full L+ crossing novelty, without assuming equal tops.
- Actual corrected physical finite numerical-H+ new-root extra-cut witness IN THE BARE original-seed closure, with I⊆old higher levels and no no-I2 premise.
- If manageable, a finite true full-Kpt-index version.
- All modules to be explicitly compiled and strict named standard-only transitive axioms checked on the same exact head; independent full repository `lake build`. Keep PR draft/stacked on C #196/#194/#192. No protected manuscript text, central imports/scripts or global validation marks.


## E47. A height-normalized old-range diary skeleton theorem

A new run with `newTop>oldTop` necessarily has selected levels ABOVE oldTop, most notably its new top. Therefore literal equality `Rold.I0=Rnew.I0` is NOT the right stability target and must never be inferred from source-profile agreement below oldTop.

The correct conclusion is **old-range restriction**:

`RunOld.I0 = {q∈RunNew.I0 : q≤oldTop}`,

and, stronger, for EVERY `i≤oldTop`,

`RunOld.I i = {q∈RunNew.I i : q≤oldTop}`.

These are actual level-set equalities, with higher new-root stages explicitly discarded. They are formulated in ONE source-coordinate tree; this does NOT yet solve the manuscript's different-generation rank normalization.

### Sufficient physical no-novelty hypothesis

Take TWO actual runs with `X⊆Y`, `oldTop≤newTop`, a REAL old seed at oldTop, and arbitrary choices of genuine Kpt monoid maps. At every `c<oldTop`, use the ACTUAL pre-cut source closures `Zold(c),Znew(c)` (which already involve the potentially different higher selected-level sets of the two runs), and suppose:

- **No NEW terminal existence:** every terminal node-at-cut event in `Znew(c)` already has some terminal witness in `Zold(c)`;
- **No NEW complete L+ crossing pair:** `Cross(Znew(c),c)⊆Cross(Zold(c),c)`, with both full old and upper types including auxiliary E.

The OLD→NEW directions are already guaranteed by exact seed/selected-level monotonicity. The assumption is therefore ONE-SIDED, as in earlier same-top Track E, and it does not require a bijection of Kpt source nodes.

### English proof

Cross-height monotonicity first gives `RunOld.I0⊆RunNew.I0`. Every old selected level is ≤oldTop by the genuine AlgorithmRun bound, so one set inclusion in the displayed old-range identity is immediate.

For the reverse inclusion take any q∈RunNew.I0 with q≤oldTop. If q=oldTop, `RunOld.I oldTop={oldTop}` and actual run final-tail identity imply q∈RunOld.I0.

If q<oldTop, suppose q∉RunOld.I0. By the actual final-tail identity in BOTH runs, q is selected at its own stage in the new run but absent at its own stage in the old run. Apply the newly verified E44 **cross-height extra-cut witness theorem**: a NEW terminal Kpt node or a NEW complete full-L+ crossing pair must occur at q.

The first contradicts the assumed no-new-terminal condition, since a terminal node in the OLD pre-cut source would make the OLD cut interesting and therefore selected. The second contradicts no-new-pair containment. Thus q∈RunOld.I0. This proves old-range final equality.

For arbitrary i≤oldTop, use the already verified `AlgorithmRun.I_eq_final_tail_of_run` for each run: membership in its i-th selected-level set is exactly membership in its final set at a level ≥i. Restricting the new final set to q≤oldTop gives the stagewise old-range equality.

**Key improvement:** this handles the true taller-root case without requiring raw selected-level equality across differing tops; it is a correct **height-filtered** diary skeleton. It separates planned new levels ABOVE oldTop from unplanned auxiliary changes in the old range.

**Hostile tests:** (1) Require a real old-top seed: the taller run may otherwise delete the artificial old top. (2) No-novelty only at cuts strictly below oldTop; top persistence is handled separately by its actual seed. (3) The tests reference the REAL pre-cut closures of both runs, not guessed equal parameter front sets. (4) The conclusion is about `I` only, not outgoing monoid maps, dependent parameter labels or a common labelled inverse-source orbit. (5) New interesting levels below oldTop are possible—K4 cuts 10/22 exemplify the danger—and then the theorem correctly reports failure of its source no-novelty assumption. (6) The old-run horizon need not equal the new-run horizon, but old/new must be literal nodes in the same normalized Kpt tree. (7) No-uniform-bound / no-BRD conclusion.

**Lean endpoints:** exact old-range final selected-set equality, then exact filtered stagewise equality from run-tail equations, both conditional on the one-sided physical no-new-terminal/full-pair certificate. These do not assume global full source-node identity.
