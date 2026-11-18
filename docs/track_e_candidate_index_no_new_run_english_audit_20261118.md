# Track E E70 — exhaustive candidate physical source index without a target AlgorithmRun

**18 November 2026. English proof and hostile audit committed BEFORE Lean.**

## Missing E69 premise

E69 reduces the construction of a synchronized AlgorithmRun on Y to finitely many actual physical candidate-source tests. Its candidate Y source at cut c uses the **OLD run's** level tail R.I(c+1), not the level sets of an assumed Y-run. It requires a FINITE exhaustive index of these true candidate closures. We must not cite E63's exhaustive index of a genuine *new* AlgorithmRun on Y: that would reinstate the circularity E69 removes.

The required index in fact follows from already verified generic finite Kpt closure bounds. The point is to choose the FINAL candidate universe `closure_(R.I 0)(Y)` and test per-cut physical membership in this same universe; **no target AlgorithmRun appears**.

## Statement E70.1

Let family be a finite normalized forbidden Kpt family; A=finiteNumericH(K,k,N) avoids family. Let X ⊆ Y be two sets of admissible Kpt nodes, both lying inside the finite-A original-prefix pool `ambientPrefixPool(family,A,hAvoid,U)` for a fixed U⊆Fin N. Assume a genuine OLD `AlgorithmRun R` on X of top h.

Then there exist finite sets oldParams and newParams of actual Kpt nodes, exact membership flags oldLive(c,i), newLive(c,j), and a single injective `φ:Fin(oldParams.card)→Fin(newParams.card)` with:

1. oldParams enumerates exactly `closure_(R.I 0)(X)`;
2. newParams enumerates exactly `closure_(R.I 0)(Y)` (**candidate final source**, no Y-run assumed);
3. for each c<h, oldLive and newLive enumerate EXACTLY their respective true pre-cut physical closures with the SAME OLD level tail R.I(c+1);
4. `newNode(φ(i))=oldNode(i)` is LITERAL source Kpt node identity, and oldLive(c,i) implies newLive(c,φ(i)) for each c<h.

Both indices are **finite in each fixed physical H+ stage**, but their sizes can grow with N and the chosen original-prefix seed sets. This is not a diary-uniform source carrier.

## Proof

**Finite level bound.** Every admissible Kpt node in X or Y is an initial segment of an actual finite-A original type with free level at most its physical original coordinate <N. Thus X,Y⊆levelLe N. The already checked generic `SMTree.Envelope.closure_finite_of_bounded` says for ANY level set I (including the OLD run's R.I0), `closure_I(Y)` is finite. No Y-run assumption enters this argument.

**Exact new index.** Convert `Znew=closure_(R.I 0)(Y)` to a Finset newParams and enumerate with `newParams.equivFin`. Put `newLive(c,j)=decide(newNode(j)∈closure_(R.I(c+1))(Y))`. For every c<h, the OLD run's final-tail identity yields `R.I(c+1)⊆R.I 0`. Closure monotonicity then gives `closure_(R.I(c+1))(Y)⊆Znew`, so every true candidate new pre-cut source has an index; conversely every active named new node belongs to that pre-cut closure by definition. No local selected-shadow approximation is used.

**Exact old index.** Apply the already verified `finiteNumericH_actualRun_uniform_exhaustive_source_index` to the ONE old run R on X, obtaining oldParams and exact oldLive. It certifies finiteness and per-cut exhaustiveness of old Kpt source nodes including all dependent meets/parameters.

**Single source identity injection.** From X⊆Y and monotonicity of physical closure with fixed R.I0, `Zold=closure_(R.I0)(X)⊆Znew`. Thus every actual old final node appears in newParams. Define φ(i) as the unique newParams enumeration index of the SAME Kpt node oldNode(i). This preserves literal full L+/E node records, not merely adjacency shadows, and is injective because the old enumeration is injective. Applying X⊆Y to the SAME tail R.I(c+1) gives oldLive→newLive at each source cut.

This is an actual CONSTRUCTION of the E69 finite-index input in each finite H+ physical stage **without having constructed the enlarged run**. It supplies neither E69's terminal exclusion nor maximal crossing old-coverage premises.

## Adversarial checks (19)

1. Only one AlgorithmRun is assumed, on X.
2. New exact closure uses the old run R.I0 and R.I(c+1), not a future RY.I.
3. Fixed finite-N physical H+ avoidance and both ambient-prefix pool bounds are required.
4. X and Y need not themselves be enumerated by a finite original-name selection; they are subsets of an ambient prefix pool with finite level bound.
5. `LevelTree.lev z ≤ N` is proved from free-level and prefix order, not assumed.
6. `SMTree.Envelope.closure_finite_of_bounded` is independent of any AlgorithmRun.
7. R.I(c+1)⊆R.I0 is obtained from genuine R's tail identity for c<h; do not assume it for arbitrary I functions.
8. newParams enumerates **final candidate closure**, not the union of selected originals only.
9. Per-cut membership uses full physical parameter-closed Kpt closure, not selected graph-age.
10. Auxiliary E, negative L atoms and meet nodes remain present in both finite universes.
11. The map φ is one old-final to new-final injection for ALL source cuts, not one choice per cut.
12. φ maps to the same physical node; a graph-isomorphic abstract type would not suffice.
13. Surjectivity is not asserted: newly generated parameter/meet nodes may enlarge newParams.
14. Old-live retention follows by actual X⊆Y at the SAME old run levels; reverse retention is not implied.
15. Per-cut old/new index sizes can differ, and Q can depend on N.
16. Existence of finite candidate index does NOT imply the candidate run satisfies Algorithm~5.4 on Y.
17. E69's maximal physical crossing old-coverage tests are still the genuine geometric gap.
18. I1 cut-level new terminal absence still needs verification; one node may terminate at its literal source level.
19. No uniform diary level bound, cross-occurrence coordinate transport, common labelled inverse-source orbit or unconditional sharp BRD is proved.

## Lean validation gate

Standalone module depending on the old actual-run source-index theorem and generic finite bounded-Kpt closure. Prove physical new final candidate finiteness, exact candidate new index, single coherent old→new index injection and exact old/new live retention. Dedicated 4-name strict transitive-axiom report with parser self-test and independent full Lean build. No protected black manuscript edits or global marker promotions until exact-head acceptance.
