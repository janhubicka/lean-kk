# Track G — crossing-pair frontier for one actual Kpt source node

**17 November 2026. English-first proof + hostile audit.** This note precedes Lean source and imports from the verified physical failure-flag and old-source retention modules only after checking exact API signatures.

## Why this differs from verified G278

G278 proves that every physically bad cut has a new-only physical Kpt node z, witnessing a new terminal or a missing COMPLETE old/upper dependent L+ crossing. It does **not** bound bad cuts by the number of new source nodes: one high-level node may have such a crossing at every lower level.

This note investigates a genuine structural restriction: **for a FIXED node z, its crossing-pair novelty cuts in two genuine AlgorithmRuns form an interval in the source cut order.** This is not a bound on the LENGTH of that interval.

## Exact definition

Work with a fixed normalized forbidden Kpt family, and two real AlgorithmRuns `Rold`, `Rnew` on possibly unrelated seed sets X,Y but in the **same** normalized tree. Their respective genuine scan tops are tOld and tNew. At `c+1≤min(tOld,tNew)` put

`Z_R(c) = closure_(R.I(c+1))(seed_R)`.

Fix a genuine Kpt node z. Define `Covered_z(c)` to mean: there exists one physical old source node w∈Z_old(c), both z and w extend to level c+1, and the ACTUAL level-(c+1) ancestors of z and w are **equal as Kpt nodes**. This is a deliberately strong condition; it implies that the complete ancestor PAIR at levels c,c+1 is identical, including all E and negative-L atoms.

Define `Live_z(c)` as z∈Z_new(c), and
`NovelCross_z(c) :⇔ c<lev(z) ∧ Live_z(c) ∧ ¬Covered_z(c)`.

The single-node crossing-pair novelty property does **not** mean that z itself is outside Zold(c); z may already lie in the old source yet its complete crossing is covered. It means z is a *live* new source witness for a full crossing PAIR that cannot be realized in the OLD source by **any** node.

## Lemma 1 — ancestor restriction

Let T be an arbitrary genuine `LevelTree`. Let a,b be nodes with
`lo≤hi≤min(lev(a),lev(b))`.
Then
`ancestor(a,hi)=ancestor(b,hi) ⇒ ancestor(a,lo)=ancestor(b,lo)`.

**Proof without a fictitious API lemma.** Put u=ancestor(a,hi)=ancestor(b,hi). The unique level-lo predecessor v of u is ≤u≤a,b and has level lo. Apply the existing `LevelTree.eq_ancestor_of_le` uniqueness lemma once to a and once to b. Both level-lo ancestors equal v. The exact upstream API is `SuccessorTree/Tree.lean`: `ancestor_le`, `level_ancestor`, `eq_ancestor_of_le`; no imported `ancestor_ancestor` lemma is assumed.

## Lemma 2 — actual pre-cut source monotonicity

For one genuine AlgorithmRun R at top t and cuts `lo≤hi<t`:
`Z_R(hi)⊆Z_R(lo)`.

**Proof:** `R.I(hi+1)` and `R.I(lo+1)` are tails of the *same actual final selected-level set*, by `AlgorithmRun.I_eq_final_tail_of_run`. Since `lo≤hi`, we have `R.I(hi+1)⊆R.I(lo+1)`. Monotonicity of full `SMTree.Envelope.closure` under selected-level inclusion and identical seed X gives source inclusion. No monotonicity of seed *sizes* or equality between old/new runs is required.

## Lemma 3 — coverage persistence and one-interval novelty

If `lo≤hi<min(tOld,tNew,lev(z))` and `Covered_z(hi)`, then `Covered_z(lo)`.
Carry the old live w down from Zold(hi) to Zold(lo) by Lemma 2, and restrict equality of the level-(hi+1) ancestors of w and z to level-(lo+1) by Lemma 1.

Similarly, `Live_z(hi)⇒Live_z(lo)` by Lemma 2 on Rnew.

For a≤b≤c strictly below both tops and lev(z), assume `NovelCross_z(a)` and `NovelCross_z(c)`. The high-cut liveness carries down to b. If z were covered at b, coverage would carry down to a, contradicting NovelCross_z(a). Hence `NovelCross_z(b)`. The set of genuine cuts on which z is live but its complete old/upper crossing pair is absent from the old source is **order-convex** (one interval, possibly empty).

The cut ordering used is the literal **common source coordinates**. No map between different numerical-H diary occurrences, no per-event node bijection, and no chosen monoid map is inferred.

## Adversarial counterchecks

1. The result is per **fixed** z, not for the union over all new Kpt source nodes. A union of disjoint intervals can have arbitrarily many components.
2. Interval LENGTH may grow with lev(z). In the abstract prefix model with an empty old source and one high new node, novelty occurs at all lower cuts; a uniform BRD bound does not follow.
3. Intersecting novelty intervals with the **old-boring** cut set may split one interval into many components. One still needs a structural compression of intermediate selected/boring levels.
4. A terminal witness z at c has `lev(z)=c`, while crossing novelty requires `c<lev(z)`. The lemma does not classify/absorb terminal exceptions.
5. A physical crossing pair is a relation, not a prescribed single-valued B3 function. All I2 forks survive.
6. Agreement of one old ancestor coordinate is insufficient without actual common node or compatible higher ancestor; here equality of the full level-(hi+1) Kpt ancestor is required.
7. No arbitrary per-cut Z_old/Z_new sets may be substituted for true AlgorithmRun closures; the crucial downward inclusion fails without the genuine selected-level tails.
8. No equality of source-node labels across different occurrences is inferred from equality of their full type records; current theorem is within one normalized Kpt tree.
9. The ancestor equality is of the actual **admissible Kpt nodes**, including dependent E and all negative L atoms. Ordinary graph-age shadows alone are weaker.
10. Correct `lo+1≤hi+1≤lev(z),lev(w)` bounds must be carried through; equality of `lo` and `hi` and the t=0 boundary must be handled.
11. A node can be in Znew at a cut without belonging to the initial seed; meets/selected parameters generated in the closure are included. Initial-seed I1 regressions are irrelevant.
12. The K4 q2=22 fixture and auxiliary cut 10 remain possible sources of new crossing intervals, never automatically boring.
13. Any claim that *one node contributes at most one interesting-level microevent* requires an extra monoid-level boring compression argument not present here.
14. A one-interval support does not itself give a finite labelled source **orbit**. Assignments of upper types to actual source names must still be transported consistently.
15. The full corrected-(B3)-loss ↔ relative-continuation equivalence and independent lower-bound colouring remain open.

## Formalization scope

Implement as a stand-alone `Kk.TrackGCrossingFrontier` module, reusing actual `AlgorithmRun.I_eq_final_tail_of_run`, `envelope_closure_mono_seeds_and_levels` and the upstream `LevelTree` uniqueness lemmas. Prove:
1. ancestor agreement restricts to lower levels (generic);
2. a true AlgorithmRun pre-cut closure grows when the cut moves down;
3. one-node old crossing cover persists when moving down;
4. one-node full physical novelty cuts are order-convex.

Run an explicit `lake build Kk.TrackGCrossingFrontier`, parser self-test, strict named standard-only axiom checks in a dedicated file. **Do not promote or annotate the manuscript as verified until exact-head direct CI passes.** The theorem would be a *conditional structural interval*, not a uniform bad-cut budget.
