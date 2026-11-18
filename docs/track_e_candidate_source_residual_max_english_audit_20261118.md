# Track E E69 — finite candidate-source frontier without assuming a new AlgorithmRun

**18 November 2026. English proof and adversarial audit written before Lean.**

## The circularity and the repair

E63–E68 compare two GENUINE physical Kpt AlgorithmRuns in the same normalized source tree. This is appropriate for tracking two already-constructed runs, but it is not a satisfactory **construction criterion** for a synchronized new run: assuming the new AlgorithmRun can put part of the desired existence conclusion into a hypothesis.

Track G's verified theorem `kpt_transport_actualRun_of_boring_only_noNovelty` is stronger: start with only a genuine OLD run on X, enlarge the seed to Y with X ⊆ Y, and use the OLD level schedule I to define the CANDIDATE pre-cut source

    Z_X(c) = closure_(Rold.I(c+1))(X),
    Z_Y(c) = closure_(Rold.I(c+1))(Y).

No new run on Y is assumed! If physical terminal and complete old/upper L+/E crossing **no-novelty** holds at all levels boring for the OLD run, the SAME I and TOTAL F create a genuine Y-run.

This note reduces this physical no-novelty premise to **one maximal residual-crossing test plus one terminal-level test per finite new-source name**. It is a bridge to the verified Track G construction theorem, not an assertion that those tests follow from the macro-diary.

## Source data

Fix a normalized Kpt tree, X ⊆ Y, oldTop h and one GENUINE AlgorithmRun R on X up to h. The candidate Z_Y(c) uses the old run R.I(c+1); NO independent or already synchronized Y-run exists in the assumptions.

Let oldNode : Fin P → KptNode and newNode : Fin Q → KptNode be fixed finite names, with oldLive and newLive Boolean per-cut flags. Assume

1. **Exact candidate NEW index:** for every c<h, z∈Z_Y(c) iff ∃j, newNode(j)=z and newLive(c,j)=true. This is the complete source including meets and dependent parameters, not selected-original shadow.
2. **Physical old-live soundness:** oldLive(c,i)=true at c<h implies oldNode(i)∈Z_X(c). Exhaustiveness of old names is NOT needed for the conditional theorem.
3. A map φ : Fin P → Fin Q with literal physical identity newNode(φ(i))=oldNode(i), not just matching ordinary-L codes. No injection is needed.

At a cut c<h call it **old boring** if the genuine predicate `¬ IsInterestingAt H (Z_X(c)) c` holds. This is stronger as a formulation than appealing to an arbitrary selected-set indicator; it matches the premise of G's run-transport theorem exactly.

For each j define the finite set C_j of cuts c<h such that

    oldBoring(c),
    c<lev(newNode j),
    newLive(c,j)=true,
    and j is NOT an old-LIVE image at c.

This is the genuine residual crossing candidate set. No independent NEW run, no externally supplied Allowed mask. Auxiliary K4 E/q2 microcuts are tested if old-boring.

## E69.1 — complete crossing pairs from one physical upper-ancestor cover

At c<h, suppose a new source node z crosses c and is covered by one w∈Z_X(c), meaning c<lev(w) and

    ancestor_(c+1)(z) = ancestor_(c+1)(w).

Equality in the ACTUAL normalized Kpt tree, not ordinary-L projection, forces equality also of their c-level ancestors by the verified G294 ancestor restriction lemma. Consequently every complete dependent old/upper L+/E crossing pair contributed by z is contributed by w in the actual old pre-cut closure. There are no I2-fork assumptions: this argument transports the **particular pair**, not a functional map of all pairs.

This is the key exact bridge between G294's per-node `covered` predicate and Track E's physical `FullPhysicalClosureCrossing` relation.

## E69.2 — one maximal residual crossing test per node

If C_j is nonempty set m_j=max C_j. Require that the physical OLD source covers the complete upper ancestor of newNode(j) at m_j. Then the verified G294 downward monotonicity of OLD run pre-cut closure and restriction of upper ancestors give the same coverage at every smaller cut c∈C_j. No new-run source monotonicity is invoked: membership in C_j already provides the actual new-live premise at each tested cut.

At an old-boring cut c, any new-live crossing j is either an OLD-LIVE image, in which case z itself is an old physical witness by identity, or residual and in C_j, and hence old-covered by the maximal test. Applying E69.1 and the exact new source index shows

    FullPhysicalClosureCrossing(family,Z_Y(c),c)
      ⊆ FullPhysicalClosureCrossing(family,Z_X(c),c).

The single-max test is sufficient; whether it is necessary for all complete crossing pairs depends on pairing different nodes of identical ancestors and should **not** be claimed as a new equivalence beyond E67's per-node formulation.

## E69.3 — the one-time terminal check

Each fixed new physical node has exactly one possible terminal cut c=lev(newNode j). Require:

    if c<h and oldBoring(c), then newLive(c,j)=false.

Then at any old-boring c the exact new index excludes EVERY new terminal in Z_Y(c). This proves the I1 terminal no-novelty condition vacuously; the old source's own terminal flag need not be reconstructed via an inferred source name matching.

The terminal and crossing tests are different: a node ending at c has no (c+1)-ancestor and cannot be handled by the max crossing test.

## E69.4 — construct the synchronized new run

Combining E69.2 and E69.3 yields genuine `NewRootNoNoveltyAtCut` at every cut boring for the OLD run, with Z_X/Z_Y computed using exactly the same OLD I-tail. Apply the fully verified Track G theorem:

    kpt_transport_actualRun_of_boring_only_noNovelty

to obtain a genuine AlgorithmRun Rnew on Y, with **Rnew.I = Rold.I and Rnew.F = Rold.F**, including the total monoid-valued F at every source-coordinate cut. The new run appears only in the conclusion, never in the hypotheses. This removes the potential proof circularity when searching for a crossheight no-novelty source certificate.

## What E69 deliberately does NOT say

The complete NEW candidate physical source indexing is still an **explicit hypothesis**. Although finite numerical-H+ ambient data should support it, E63 currently provides its index for a *genuine new run*, which cannot be fed blindly into this no-new-run construction. A separate finite closure-of-old-I-on-Y lemma is needed to discharge this premise in the resolved numerical-H+ application.

Also still missing: the maximal residual physical coverage and terminal tests for the ACTUAL resolved-diary Henson construction, uniform diary-dependent bounds on physical nodes and microcuts, source-coordinate normalization across two independent occurrences, transported assigned successor characters and labelled dependent parameter recipes, and one common labelled inverse-source monoid orbit. This is not an unconditional upper BRD theorem.

The K4 auxiliary cuts 10/22 are neither erased nor deemed boring; if one is genuinely old-boring it must pass the physical tests.

## Adversarial audit (21)

1. There is exactly ONE assumed genuine AlgorithmRun, on X.
2. The new source closure is evaluated at the OLD run's I(c+1), not a guessed Y-run I.
3. The old and new sources live in the SAME normalized Kpt tree.
4. X⊆Y is needed by Track G's ultimate run transport, but not by the local pair transport lemma.
5. The old-boring predicate is the actual full-source IsInterestingAt, not selected graph-age boringness.
6. A cut c=h is never tested, only 0≤c<h.
7. newLive MUST be exact over the candidate source at each old cut.
8. oldLive soundness suffices for matching old-image names; old index completeness need not be asserted.
9. Old/new finite node-name lists can differ in size; phi need not be surjective.
10. phi must preserve actual physical node identity; ordinary adjacency code alone is insufficient.
11. No inverse-source map is chosen for each new Kpt node.
12. At an I2 fork the crossing relation is set-valued, and one matched physical upper ancestor is enough to transport each particular pair.
13. Equality of upper Kpt ancestors supplies BOTH old/upper full L+/E pairs (not two marginal witnesses).
14. An old-LIVE image is automatically covered by the same actual node.
15. A residual crossing may be old-final early-live or genuinely new-final; neither is ignored.
16. The maximal residual cut may be disconnected from other residual cuts by old-interesting levels; old physical coverage still transports downward.
17. New candidate source monotonicity is NOT needed for the max test; old run source monotonicity is sufficient.
18. A terminal node c=lev(z) must be checked separately; it cannot be forced through the crossing branch.
19. There is one terminal-level check per physical name and at most one maximal physical crossing test per name; this is NOT a uniform diary bound because Q may depend on ambient N.
20. Auxiliary K4 q2/E events at cuts 10/22 are still genuine potential source cuts; no blanket Allowed exceptions.
21. The final run construction does not identify two arbitrary different diary occurrences or prove the common labelled inverse-source orbit.

## Formalization and validation acceptance

Formalize E69.1 full-pair transfer, E69.2 candidate finite residual max, E69.3 terminal exclusion, and E69.4 actual run existence. Add direct named `#print axioms` checks, standalone module build and independent full Lean CI. Preserve English before Lean; remain draft until exact-head green. Do not alter frozen black mathematics or promote global manuscript validation markers.
