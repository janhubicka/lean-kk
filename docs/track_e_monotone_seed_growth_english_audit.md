# Track E — monotonicity of genuine Algorithm 5.4 under Kpt seed growth

**14 November 2026, English argument and adversarial checks before Lean.** Based on integrated `lean-kk` main `f17b42f0b5490245a2e61b0fccaa6437ea1f776f` (including completed Track E #138/#158, actual-run Track D). Parent manuscript [Track E #27](https://github.com/janhubicka/Counting-big-Ramsey-degrees-of-K_k-free-graphs/issues/27). This is a new-root *one-sided* theorem, not an assumed full cross-occurrence equality.

## E29. Generic minimal closure is monotone in both source seeds and selected levels

Let `S` be an actual successor tree, `I⊆J` sets of selected parameter levels, and `X⊆Y` actual node seed sets. Then

`closure S I X ⊆ closure S J Y.`

**Proof:** `C=closure S J Y` is meet-closed and parameter-closed over J, hence parameter-closed over I; moreover X⊆Y⊆C. Minimality of `closure S I X` yields the inclusion. This is about the GENUINE meet-and-parameter closure defined by intersections of closed supersets, not a simulated selected-front subset.

## E30. Actual semantic interestingness is MONOTONE in its full source closure

For ANY genuine `H : SMTree S`, arbitrary sets `Z⊆W` of physical tree nodes, and any cut c,

`IsInterestingAt H Z c → IsInterestingAt H W c.`

**Proof:** In the actual definition, the (I1) presence and (I2) same-component-meet disjuncts are existential and their real witnesses survive set inclusion. The (I3) disjunct says **no genuine monoid map** skips c while respecting every crossing in Z. If the larger W had such a map, exactly that SAME map would respect every old z∈Z, contradicting the I3 obstruction. The monoid membership, skip law and full ancestor equations are retained literally.

This requires no corrected-(B3) equivalence, no ordinary-L age test and no no-(I2) assumption. It is a direct universal source property and applies even when the new closure contains fake E-dependent parameters.

## E31. Genuine AlgorithmRuns: enlarging seed set can only ADD interesting levels

Let `X⊆Y` be genuine node seed sets of the **same** admissible normalized Kpt tree. Let `R_X` and `R_Y` be two ACTUAL AlgorithmRuns with the **SAME top/horizon** `top`; their one-level skip maps and choice functions are unrestricted. Then

`∀ i≤top, R_X.I i ⊆ R_Y.I i.`

In particular, the actual **final** selected-level sets satisfy
`R_X.I 0 ⊆ R_Y.I 0`.

**Backward induction:** At the top both runs have I(top)={top}. Suppose I_X(i+1)⊆I_Y(i+1). The actual closure monotonicity E29 gives the pre-cut inclusion
`closure S (I_X(i+1)) X ⊆ closure S (I_Y(i+1)) Y`.
If i is interesting for X, E30 implies it is interesting for Y; the genuine `interesting_step` laws select i in both, and `insert` preserves subset. Otherwise, the old run's `noninteresting_step` gives I_X(i)=I_X(i+1), while the new run always satisfies I_Y(i+1)⊆I_Y(i) (whether it inserts i or not). Hence induction closes.

This is stronger than the earlier Track E conditional *equality* of level sets given matching terminal/crossing profiles. **No cross-occurrence profile equalities are assumed here.** The result is inherently one-sided, as newly inserted seeds may generate genuinely new (I1)/(I2)/(I3) cuts. Same top is essential; comparison of runs with different physical horizons must first pad/align them.

## E32. Concrete closure-plus-new-root transition

For a fixed earlier selected set I, let `Y = closure S I X ∪ W`, where W is any set of genuine NEW Kpt roots or their prefixes. Then **X⊆Y by construction**: every original old seed belongs to the genuine closure. Hence any two actual same-horizon runs on X and Y satisfy selected-level inclusion.

Applied to Track C [new-root PR #165](https://github.com/janhubicka/lean-kk/pull/165), W may be the actual `ambientPrefixPool` of physically inserted originals in the extended finite numerical H+. All old seeds, complete meet/parameter closure nodes, and new root prefixes are retained. This theorem does not construct such a physically valid extension; C's actual avoidance and representation hypotheses are indispensable. But **once** such a genuine next seed set and same-horizon runs exist, selected levels cannot disappear under the extra roots.

## E33. Every NEW selected level requires a NEW physical full-source witness

For same-horizon actual runs on `X⊆Y`, choose a cut `i<top` which is selected by the larger run **at stage i** but absent from the smaller run at stage i:

`i∈R_Y.I i,quad i∉R_X.I i.`

Write `Z_X=closure S (R_X.I(i+1)) X` and `Z_Y=closure S (R_Y.I(i+1)) Y`. E31/E29 give `Z_X⊆Z_Y`. Because the algorithm's interesting branch MUST select i, and its noninteresting branch MUST skip i, the displayed membership conditions imply `¬IsInterestingAt H Z_X i` and `IsInterestingAt H Z_Y i`.

Then one of the following **concrete novelties** must occur:

- **New terminal witness:** a genuine Kpt node z∈Z_Y but z∉Z_X with level(z)=i.
- **New full L+ crossing pair:** a literal old/upper pair (T,U) in `FullPhysicalClosureCrossing family Z_Y i` which is absent from `FullPhysicalClosureCrossing family Z_X i`, including every auxiliary E bit and negative L atom.

**Proof:** Suppose no new terminal witness. Since terminal I1 is existential and Z_X⊆Z_Y, the two terminal flags agree (and both are in fact false because smaller cut is not interesting). Suppose also there is no newly occurring pair. Inclusion of the sets of closure nodes implies inclusion of their full crossing relations; absence of new pairs gives equality. The already verified Track E genuine monoid theorem `kpt_actual_interesting_iff_of_terminal_and_crossing_eq` then identifies the IsInterestingAt verdicts, contradicting old boring/new interesting. This gives a *physical diagnostic* for each extra selected level, not merely “the new run chose it.”

**Finite numerical H+ consequence:** Track C's real exhaustive run index enumerates every z∈Z_Y and the complete per-cut `Option RawPartialTypeNode` pair of each crossing. The novelty witness can therefore be searched for entirely among the finitely many ACTIVE new-source node indices. A literal finite-index corollary needs the exact current-run index coverage certificate; it must never replace Z_Y by selected F-vertices.

### Adversarial checks

1. **Same top:** the two genuine runs share a source-level horizon. A new higher top may insert different levels just by changing the scan interval; it is not covered.
2. **Actual monotone seeds:** X⊆Y must be literal as Kpt nodes. Mapping old numerical vertices into a new coordinate system without proving equality of full Kpt L+ codes is not enough.
3. **Selected-level inclusion is not equality:** a newly inserted root can create an I1 terminal, an I2 meet, or I3 monoid obstruction. The proof does not forbid them.
4. **Auxiliary E:** the Kpt node and physical crossing pair carry complete L+ types. A graph-L-only shadow cannot certify absence of new I3 constraints.
5. **No fake ages:** no E is assigned to any auxiliary finite L-only B3 age witness.
6. **Not all added nodes trigger a new level:** duplicate old crossing pairs and redundant terminal levels may be invisible; earlier Track E closure-blindness regressions show why.
7. **No uniform finite carrier:** each real run's exhaustive index can grow with ambient N and new roots.
8. **No map/orbit equality:** monotonicity compares only selected `I` sets; the chosen `F` monoid maps can differ, and even identical interestingness does not reconstruct named source nodes.
9. **No fixed-seed artifact:** the real resolved schedule changes X, so the earlier same-seed prefix stability theorem cannot substitute for this new-root monotonicity.
10. **No claim full diary theorem:** proving “no added terminal/crossing witnesses at every cut” from the actual resolved macrodiary, and identifying a single common labelled inverse source, remain open.
11. **Stage index vs final:** the first local novelty theorem uses i∈I_Y i and i∉I_X i. To specialize to final I0, the true AlgorithmRun final-tail identity must be invoked.
12. **I1 priority:** raw I2 can be true at a self-meet terminal level; novelty theorem uses the actual disjunction `IsInterestingAt` rather than an unqualified I2⇔fork.

**Validation contract:** commit this English proof before Lean source. Direct exact-head build of the new module and strict named standard-only transitive-axiom parser, independently of the full repository `lake build`. Do not edit frozen manuscript text, central `Kk.lean` imports or global validation marks.

## E34. FINITE live-index certificate for every extra cut of an actual numerical H+ run

Track C's merged `finiteNumericH_actualRun_uniform_exhaustive_source_index` **constructs** one genuine finite index `Fin params.card` of all dependent Kpt nodes of the final closure of a real finite numerical-H+ AlgorithmRun, with a per-cut Boolean activity mask exact for its physical pre-cut closure. Thus the E33 novelty alternatives need not remain unindexed existential node-set claims.

Let `Y` be the genuine larger Kpt seed set of a real numerical-H+ structure `A=finiteNumericH K k N`, with an explicit original-prefix representation `Y⊆ambientPrefixPool family A hAvoid U`. Let `X⊆Y` be the old seeds, and let actual same-top Kpt AlgorithmRuns `RunX,RunY` exist. At any cut `c<top` that `RunY` selects but `RunX` skips, construct, **from the actual RunY source**, one finite `params`, one `live(c,j)`, and one of:

1. an actual live index j whose node `params[j]` is **not** in the old run's pre-cut closure and whose level is exactly c; OR
2. an actual live index j and full dependent raw types `(T,U)`, such that
   `kptFullOldAtCut(params[j],c)=some ⟨c,T⟩`,
   `kptFullUpperAtCut(params[j],c)=some ⟨c+1,U⟩`,
   and `(T,U)` does **not** occur in the old run's canonical complete crossing relation at c.

**Proof:** E33 supplies a real new node or real new crossing pair. The *constructed* exhaustive index gives a live index for the node, or, through verified `indexed_physical_crossing_eq_full_closure_relation`, a live index witnessing the complete pair. The same j supplies both old and upper records; fake E and all absent atoms are preserved. No artificial finite witness of graph age is introduced. The final-level version follows from the actual `AlgorithmRun.I_eq_final_tail_of_run`: for any 0≤c<top, `c∈Run.I 0` iff `c∈Run.I c`.

The resulting finite source-index universe is **not uniformly bounded across ambient N**, and the selected source labels / parameter-incidence relations still need to be transported to obtain a fully labelled orbit. This is, however, an auditable finite physical obstruction certificate for every extra interesting cut in a genuinely resolved new-root extension.

**Hostile tests:** (a) live≠crossing; first alternative includes terminal live nodes and second requires both *non-none* ancestor Options from the SAME j; (b) never substitute the old run's finite index for the new complete closure index; (c) strict `c<top` is needed for the pre-cut run stage; (d) no-(I2) is not assumed—multiple upper records are kept; (e) the hypothesis `Y⊆ambientPrefixPool` is a real physical representation obligation, discharged by Track C's actual new-root construction only after its avoidance/new-root input checks; (f) no selected F shadow; (g) if new closure has redundant terminal prefixes, extra events need not follow and the theorem asserts only the implication from new selected levels; (h) no automatic diary canonicality.


## E35. A ONE-SIDED stability certificate for true new-root AlgorithmRuns

The preceding E31 proves `Run_X.I i⊆Run_Y.I i` for actual same-top runs whenever X⊆Y. In particular, at every actual pre-cut stage the full Kpt source of the old run is contained in the full Kpt source of the new run, even if their higher selected-level sets do not coincide.

Therefore to prove the **opposite inclusion** of selected levels, symmetric source comparisons are unnecessary. It suffices to certify, for every source-coordinate cut `c<top` in the two real runs, the following two **one-sided absence-of-novelty** facts, where
`Z_X(c)=closure (Run_X.I(c+1)) X` and
`Z_Y(c)=closure (Run_Y.I(c+1)) Y`:

1. **No new terminal I1 witness:** whenever `Z_Y(c)` contains ANY node ending at c, `Z_X(c)` already contains a node ending at c. This does not require the two witness nodes to be identical.
2. **No new full crossing pair:** `FullPhysicalClosureCrossing(Z_Y(c),c) ⊆ FullPhysicalClosureCrossing(Z_X(c),c)`. This compares the complete dependent old+upper L+ pair, with auxiliary E and ALL old parameters, not merely the set of next ordinary-L reducts.

Then the actual source inclusion from E31/E29 gives the REVERSE implications for both terminal existence and crossing pairs automatically. Thus the actual physical terminal and crossing profiles are equal at each cut, and the verified `two_actual_Kpt_runs_level_sets_eq_of_stagewise_full_profiles` backwards-induction theorem yields

`∀ i≤top, Run_X.I i=Run_Y.I i`.

This is a genuinely more economical **new-root stage certification** than proving source-graph equality in both directions from scratch. The mathematical work left for the resolved diary is to show that its newly inserted physical original roots satisfy the two no-novelty conditions at all cuts which are *supposed* to stay boring or retain their event status. At a planned new diary event, the finite novelty theorem E34 identifies exactly which new terminal/full-crossing witness needs to be accounted for.

### Finite indexed form

Use one exhaustive *finite new-run Kpt source index* `node : Fin params.card→Kpt` and its exact `live(c,j)` mask, supplied by Track C's real numerical-H+ source theorem. Instead of comparing arbitrary sets of physical crossings, check the following on **every live index j**:
- if `lev(node j)=c`, old `Z_X(c)` already has *some* node terminating at c;
- if `kptFullOldAtCut(node j,c)=some ⟨c,T⟩` and `kptFullUpperAtCut(node j,c)=some ⟨c+1,U⟩`, then `(T,U)` already belongs to the old physical crossing relation.

The previously verified finite-index/physical-relation equality turns these checks into the two no-novelty conditions. Therefore all selected levels of the two real runs agree. This is an **application-ready FINITE verification interface** for a full physical new-root stage once its old/new Kpt source node names and source-cut normalization are constructed. It still does NOT bound `params.card` uniformly across ambient N and does not prove a common labelled inverse-source orbit.

### Additional hostile checks
- The no-novelty condition is SUFFICIENT, not necessary for selected-level equality: one may add a new crossing that the genuine Kpt monoid can still skip, or a duplicate terminal node at an already-interesting cut.
- Full pair containment is stronger than equality of B3 verdicts; the I3 obstruction depends on actual complete Kpt source crossing equations.
- The tests use `Run_X.I(c+1)` and `Run_Y.I(c+1)` as calculated by the **real runs**, not an externally guessed shared level set.
- If the new-run full source index is incomplete or its live mask is restricted to marked selected vertices, the conclusion is invalid.
- Same top and literal source-level alignment remain necessary. The unbounded resolved-copy construction may increase the top or alter the generation k.
- Equality of the selected-level skeleton does NOT itself determine the selected+auxiliary parameter label correspondence or the real monoid-map pullback orbit.

**Lean targets:** actual two-run one-sided no-novelty theorem and a corresponding exact-full-index criterion. The latter must use the existing verified exhaustive current-run index, never a guessed set of original names. Strict isolated direct build and named standard-only transitive-axiom reports before any validation claim.


## E36. Entirely FINITE two-index physical NEW-ROOT stabilization test

The E35 finite criterion still tests whether the new index's old/upper pair lies in the old **set-valued** crossing relation. Track C constructs an exhaustive finite Kpt index for BOTH actual finite numerical-H+ runs. We can therefore eliminate the remaining infinite-set membership from the verification interface.

Fix actual same-horizon `Run_X` and `Run_Y` with literal X⊆Y. Take two possibly different finite source universes
`node_X : Fin p→Kpt`, `node_Y : Fin q→Kpt`
with exact pre-cut presence masks `live_X(c,i)`, `live_Y(c,j)`. Each exactness statement says a node belongs to its actual full meet-and-parameter pre-cut closure **iff** it is one of the live finite node values at that cut.

For EACH cut c<top and EACH new-live index j, perform just two finite source checks:

**Terminal coverage:** If `lev(node_Y j)=c`, there exists some old-live index i with `lev(node_X i)=c`. No node identity or multiplicity match is needed to keep the Boolean (I1) flag fixed.

**Full transition coverage:** Whenever the complete old and upper Kpt raw type assignments of `node_Y j` at c exist, say `(T,U)`, there is some old-live index i whose complete old and upper raw assignments are **exactly the SAME pair `(T,U)`**. The two records for either index come from the SAME genuine Kpt node, retaining all E/negative atoms and potential I2 forks. The relation of old/new label numbers is not required to be a function, injection or bijection—duplicates may collapse to the same physical pair.

Then **all selected-level sets of the two real runs coincide**. The proof composes E35's exact-new-index criterion with the actual old-index coverage: terminal matches give genuine old terminal witnesses; matching old `Option RawPartialTypeNode` records give membership in the old `IndexedPhysicalCrossing`, which equals the full canonical physical crossing relation by the already certified Track E source-index theorem.

This is a **finite `∀j∃i` test**, directly available for the actual finite numerical-H+ closure indices constructed in Track C, and is the smallest concrete input needed for an *inert* new-root extension at a fixed horizon. The two finite index sizes may differ. No global uniform bound is inferred; an actual resolved-copy construction may have deliberate newly interesting cuts, which must be treated as planned exceptional events rather than erroneously required to be inert.

**New hostile cases:** preserve each source's *cut-specific* live mask; old final-closure membership alone does not imply pre-cut activity. Comparing only complete UPPER L-reducts loses old dependent-L+ source identity and cannot transfer genuine I3 skipping maps. Requiring a bijection of all nodes is unnecessarily strong for the selected-level skeleton, but may remain essential for full labelled orbit. This criterion is sufficient, not necessary; an extra pair may be skippable. It is source-coordinate-dependent and says nothing about inserted boring gaps until those coordinates are actually normalized.

Lean target: a lemma deriving E35 from two exact finite index representations and the two finite coverage conditions, followed (optionally) by a separate genuine finite numerical-H+ constructor theorem that invokes Track C's source-index construction on each run. English proof and adversarial qualifications precede Lean, with strict exact-head axiom checks required.
