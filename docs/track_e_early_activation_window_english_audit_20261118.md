# Track E E66 — early activation of an old-final Kpt node is an interval, not one cut

**18 November 2026. English-first proof and adversarial audit, committed before Lean.**

## Position in the now-merged argument

E63 constructs one coherent injective old-final→new-final Kpt name map for genuine nested finite numerical-H+ AlgorithmRuns. E64 reduces reverse physical no-novelty to residual NEW-LIVE names, and E65 splits them into two classes:

1. a genuinely new FINAL Kpt name (outside the image of old-final names), or
2. an OLD-FINAL name, which is nevertheless INACTIVE in the old PRE-CUT source and ACTIVE in the new PRE-CUT source.

Track G's G294/G298 proves different results about a single **uncovered complete old/upper L+ crossing**: its fixed-node uncovered crossing cuts form an interval (under the exact hypotheses). It does not explicitly describe the LIVE/NOT-LIVE activation window of the second E65 class.

## E66.1 — the Boolean order-convexity lemma

Fix arbitrary old/new Boolean live masks and a map φ:Fin P→Fin Q. At cut c, define

    Early(c,j)  :=
      newLive(c,j)=true
      AND ∃i:Fin P, φ(i)=j AND oldLive(c,i)=false.

This is **E65's old-final newly active condition plus the missing NEW-LIVE premise**. Do not call E65's bare KptEarlyOldFinalName alone "newly active"; it can hold for a currently inactive new node.

Assume the two masks are downward monotone in the literal source-coordinate scan order:

    low≤high<oldTop, oldLive(high,i)=true
       ⇒ oldLive(low,i)=true,
    low≤high<oldTop, newLive(high,j)=true
       ⇒ newLive(low,j)=true.

Then whenever low≤mid≤high<oldTop and Early(low,j) and Early(high,j), we have Early(mid,j).

**Stronger proof:** actually only Early(low,j) and newLive(high,j)=true are needed. Choose the old index i witnessing Early(low,j). The new-high liveness forces new-mid liveness by downward monotonicity. If old-mid were true, monotonicity would force old-low to be true, contradicting the same witness's old-low false. Thus the same i proves old-mid false. No injectivity of φ, surjectivity or old→new liveness is needed for this *Boolean* interval fact; those stronger assumptions are needed for the physical interpretation of the name map.

This says each fixed mapped old-final node's early-live cuts form an order-convex subset of the common old scan range. Empty windows and singleton windows are possible.

## E66.2 — a genuine Kpt AlgorithmRun version

Let R and Q be **genuine** normalized-Kpt AlgorithmRuns in the same Kpt tree, with oldTop≤newTop. Fix arbitrary finite Kpt source naming functions oldNode/newNode and per-cut oldLive/newLive masks, each **exact per-index**:

    oldLive(c,i)=true ⇔ oldNode(i)∈closure_(R.I(c+1))(X);
    newLive(c,j)=true ⇔ newNode(j)∈closure_(Q.I(c+1))(Y).

For every old-range cut c, these are actual full Kpt meet-and-parameter closures (not selected-front graph-age shadows). The checked G294 \`kpt_actual_run_preCut_source_mono_down\` shows each closure grows as the cut decreases; exact source membership produces the two downward mask monotonicity hypotheses above. Apply E66.1 to obtain order-convexity of Early(c,j) for EVERY fixed new index j.

This physical lemma requires actual AlgorithmRuns and exact per-index masks. Literal X⊆Y and a real old-top seed are **not needed just for the interval property**; they are required earlier to construct/interpet the genuine old→new physical φ from E62/E63. Do not sneak those omitted hypotheses back into the interval lemma.

## E66.3 — a hostile unbounded-length abstract mask regression

For arbitrary n≥1, choose one old-final name and one new name with φ the identity, oldLive(c)=false and newLive(c)=true at all c<n. Both masks are downward monotone; Early(c,0) holds for **every** c<n. Thus even a SINGLE early-activated old-final name can cover n different cuts in this Boolean abstraction. There is no interval-length bound from just the number of old-final names, the monotonicity, or the E65 dichotomy.

This is **not** asserted to be realized by two genuine Kpt AlgorithmRuns with the old-final naming generated in a particular numerical-H+ source. An actual geometric restriction could bound or remove some windows. It is a countermodel to the logically invalid deduction "one activation interval = one interesting cut" from the present abstract hypotheses.

## Adversarial checklist (18)

1. \`KptEarlyOldFinalName\` alone does not include NEW-LIVE; E66 adds it.
2. Finite indices and actual Kpt source nodes are different objects.
3. φ need not be injective for Boolean convexity; E65's classification uses injectivity.
4. If φ is a genuine identity-preserving physical name map, a mapped index denotes an old FINAL source node.
5. Old-final membership does not imply old PRE-CUT live membership.
6. New-live at a higher cut implies new-live at every lower cut in an actual run.
7. Old-INACTIVE at a lower cut forces old-INACTIVE at every higher cut, by contraposition.
8. One node's early-activation window can be empty.
9. It may have arbitrary length under monotone-mask assumptions.
10. An interval of source CUTS need not correspond to one macrodiary transition.
11. These are literal source coordinates; unrelated numerical H+ generations still need a cut reindexing map.
12. Full source membership is stronger than selected graph-age presence.
13. The interval property gives no NEW→OLD terminal or full crossing-pair cover.
14. Same-node complete old/upper L+ crossing novelty can persist across many cuts, even for one new physical node.
15. Track G's G294 one-node crossing interval and E66's activation interval are distinct, compatible results.
16. The interval's intersection with the set of old-boring cuts may be disconnected.
17. K4 E/q2 microcuts 10 and 22 must be retained; this theorem cannot dismiss them as exceptions.
18. No uniform finite diary orbit, labelled carrier, BRD upper bound or independent lower degree follows.

## Remaining substantive geometry

Prove using actual resolved numerical-H+ Henson construction that BOTH residual classes from E65 have no newly uncovered complete old/upper dependent L+ crossing or terminal at old-boring cuts outside a diary-controlled, uniformly bounded set of E/q2 microevents; also align the cut maps and the full assigned successor characters across distinct occurrences. E66 describes the possible **shape of early activation**, not why those intervals are harmless.

## Validation plan

Use a standalone Lean module importing E65 and G294. Prove a Boolean order-convexity lemma, its genuine Kpt AlgorithmRun specialization under exact per-index membership, and an abstract long-window regression. Direct \`lake build\`, strict exact-head named \`#print axioms\` audit and independent full build before adding even a BLUE manuscript validation marker. Frozen black manuscript sentences untouched; do not reinsert TODOs removed by Sofia.
