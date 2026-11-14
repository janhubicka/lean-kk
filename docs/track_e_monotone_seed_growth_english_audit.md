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