# Track E E68 — residual maximal-frontier reduction for genuine Kpt runs

**18 November 2026. English mathematical proof and adversarial audit, committed BEFORE Lean.**

## Motivation and exact scope

E63 builds one coherent old-final to new-final physical Kpt index for two genuine nested numerical-H+ runs. E64 says that at an old-boring cut, any genuinely NEW terminal or unmatched complete old/upper L+ crossing must have a NEW-LIVE index outside the image of OLD-LIVE indices. E65 distinguishes (a) new final index names from (b) old-final names newly active at the cut. E67 proves that for ONE fixed actual new Kpt node, complete old crossing coverage at its maximal eligible source cut implies coverage at every earlier eligible cut.

An initial temptation was to remove OLD-LIVE image names before computing the E67 frontier, on the theory that a higher cut could be harmless (old-live) but a lower cut still newly active. **Adversarial correction:** in the genuine exact old-live index this situation is impossible: old pre-cut source membership, hence the exact old-live mask, grows as source cuts decrease. In particular an old-live higher cut cannot be followed by a residual lower cut. The filtered certificate below is valid already with one-way old-live soundness, but **is not a stronger geometric certificate than E67**. The more useful new observation, proved in E68.4, is that exact physical masks make the residual eligible support upward-closed and force its maximum to equal the unfiltered maximum whenever nonempty.

## Exact data

Fix one normalized Kpt tree and two **genuine** AlgorithmRuns Rold on seeds X up to oldTop and Rnew on seeds Y up to newTop. No nesting of X and Y is required just for this proposition.

Fix finite sets of names Fin P and Fin Q, physical node functions oldNode and newNode, a map phi : Fin P -> Fin Q, and oldLive : Nat -> Fin P -> Bool, with:

(H1) newNode(phi(i)) = oldNode(i) for every old index i (literal node identity).

(H2) if c < oldTop and oldLive(c,i)=true then oldNode(i) is in the **full genuine old pre-cut source** closure_(Rold.I(c+1))(X).

Neither surjectivity nor injectivity of phi is needed for the fundamental reduction. E63 supplies both H1 and H2, plus injectivity, when the finite index is derived from actual nested numerical-H+ runs.

Let E_j be the E67 finite set of cuts for z=newNode(j): those c < min(oldTop,newTop) which are old-boring, outside Allowed, satisfy c < lev(z), and have z in the genuine new pre-cut closure.

Define the **residual eligible frontier** for the named node j:

    R_j = { c in E_j : there is NO i with oldLive(c,i)=true and phi(i)=j }.

This is a finite subset of E_j. It uses old LIVE images at the actual cut, not the old FINAL image. The definition retains all genuine auxiliary E and Kpt parameter nodes and all old/upper dependent L+ types.

## Lemma E68.1 — old-live image nodes automatically have a complete physical crossing witness

If c < oldTop, c < lev(newNode j), and some i has oldLive(c,i)=true and phi(i)=j, then newNode(j)=oldNode(i) belongs to the genuine old pre-cut closure by H1–H2. Taking w=newNode(j) itself as witness, its full upper (c+1)-Kpt ancestor equals itself's ancestor. Hence the exact G294 predicate Covered(newNode j,c) holds.

This preserves the **same** complete old/upper type pair, including dependent auxiliary E and negative ordinary L, with one physical witness; no separate matching of marginal types, selected shadow, or guessed inverse node map occurs.

## Theorem E68.2 — all eligible crossings iff one residual maximal cut per name

The following are equivalent:

(A) For EVERY new physical name j and EVERY c in E_j, Covered(newNode j,c) holds.

(B) For every new name j whose residual set R_j is nonempty, Covered(newNode j,max R_j) holds.

Proof of (A) => (B): max R_j belongs to E_j. Apply (A).

Proof of (B) => (A): fix j and c in E_j.

* If j is an old-live image at c, apply E68.1: w=newNode(j) is already a physical old source witness.
* Otherwise c is in R_j, so R_j is nonempty and c <= m=max R_j. By (B), the old full crossing pair of newNode(j) has one old physical witness at m. Since m belongs to E_j, m<oldTop. The verified G294 monotone-down lemma restricts this SAME old witness to cut c, preserving exact upper ancestor equality. Thus Covered(newNode j,c).

This equivalence is a useful factorization through residual names even when only one-way old-live soundness is known. **It does not strengthen the physical E67 crossing criterion.** If the old-live mask is exact and downward monotone, a maximal eligible old-live cut means ALL lower eligible cuts are old-live too, so the residual set is empty. If the residual set is nonempty, its maximum equals the unfiltered maximum. The apparent possibility of a harmless higher cut hiding a genuinely uncovered lower residual cut is therefore a DEAD END, not a new obstruction.

## Corollary E68.3 — the two genuine E65 residual kinds remain

If phi is additionally injective, each c in R_j satisfies precisely the E65 dichotomy:

* j is outside the image of ALL old FINAL names; or
* j is a matched old FINAL name whose old pre-cut live flag is false at c.

The second possibility must NOT be discarded as harmless. In particular an old-final node may have a long early activation interval (E66), so one residual maximum does not mean one interesting cut or one diary event.

## Theorem E68.4 — exact live-mask monotonicity collapses both frontiers

Add the genuine old-mask downward monotonicity assumption:

    (H3) low <= high < oldTop and oldLive(high,i)=true
         imply oldLive(low,i)=true.

H3 is not a new global diary hypothesis: it follows from the verified G294 old pre-cut closure monotonicity when oldLive is an **exact per-index** representation of the actual physical old source, as in E63 (and is proved for exact actual runs in E66). Mere soundness H2 does NOT suffice for H3.

**Claim A (relative upper closure).** If c is residual eligible for j, d is eligible for the same j and c <= d, then d is residual too.

Proof. Suppose instead that some old name i has oldLive(d,i)=true and phi(i)=j. Eligibility gives d<oldTop. By H3, oldLive(c,i)=true, contradicting the residual definition at c. Hence d is residual.

**Claim B (coincident maxima).** If R_j is nonempty, then E_j is nonempty and

    max R_j = max E_j.

Proof. R_j is contained in E_j. Let c=max R_j and d=max E_j; then c<=d. Claim A implies d is residual. Thus d<=max R_j=c, so d=c.

**Claim C (vacuous alternative).** If E_j is nonempty but max E_j is old-live matched, then R_j is empty. The same witness is old-live at every lower eligible cut by H3, so all E_j crossings are physically covered by E68.1.

This identifies a genuine simplification: in the actual E63 setting there is **no need to maintain two different cut frontiers**. One can use E67's original maximal eligible cut; E64/E65 tell us whether its test is automatic (old-live image) or remains an actual residual geometric obligation. Early old-final activation windows (E66) can still be long; the theorem says nothing about how often their original Kpt nodes cross eligible cuts or whether they are covered.

**Hostile regression.** Under soundness H2 alone, one could deliberately set an old-live mask to false at a low cut even when its physical node is genuinely old-live there, and true at a high cut. Then the algebraic residual filter can exhibit a different maximum, but ALL physical crossings below the matched high cut are already covered by G294. This is an **inaccurate finite mask**, not a valid exact E63 index and not a counterexample to the diary theorem.

## Explicit limitations

The theorem is an exact equivalence for **physical crossing coverage of the finitely named new nodes**. To turn it into the genuine no-novelty result at every old-boring off-plan cut, a later application must (i) use E63's exhaustive exact NEW source index, (ii) separately exclude cut-level I1 terminals, and (iii) connect the physical Covered predicate to the full indexed relation (E54/E64). None of those application steps is silently bundled into this theorem.

There is still NO uniform bound on the number of names Q, the size of R_j, its height, the number of old-boring microcuts, the diary carrier, or the size of a common labelled inverse-source monoid orbit. The K4 auxiliary E/q2 source cuts 10 and 22 are not dropped or declared automatically harmless. Cut coordinates from unrelated diary occurrences are not identified.

## Hostile checks

1. BOTH AlgorithmRuns are genuine; arbitrary level masks cannot supply the G294 downward closure lemma.
2. Common physical Kpt tree and literal source coordinates are required.
3. Eligibility uses min(oldTop,newTop), even if the new run is shorter.
4. Old-boringness belongs to Rold.I(c), not Rnew.I(c).
5. Allowed can be any set, including empty, all cuts, or a disconnected set.
6. The terminal case c=lev(z) is excluded and must be checked separately.
7. The crossing case has c<lev(z), ensuring a genuine (c+1) ancestor.
8. FULL parameter-closed new source membership is used, not a selected original-name shadow.
9. FULL physical old source membership for old-live names is essential to E68.1.
10. Merely sharing an ordinary adjacency column does not imply H1.
11. The physical identity witness w=z needs no chosen inverse source or functionality.
12. No I2-fork uniqueness assumption enters the proof.
13. The residual filter uses OLD-LIVE images, not the image of the whole final old index.
14. The residual set R_j may be empty even if E_j is nonempty: then every eligible cut is old-live-covered.
15. R_j need not be an interval after removing allowed or old-interesting cuts.
16. The maximal member exists only when R_j is nonempty.
17. Downward OLD coverage is applied in the correct direction, max to smaller cut.
18. The old-live status at c and m can differ; the theorem never assumes constant liveness.
19. Injectivity of phi is not used in E68.1/E68.2; it IS required for the E65 two-class converse.
20. No numerical-H+ diary realization, arbitrary-occurrence normalized orbit, global Ramsey upper bound or sharp BRD is claimed.\n21. H3 must be obtained from exact old-live masks; one-way old-live soundness H2 does NOT imply H3.\n22. Under H3 the residual support is relatively upward-closed and its maximal cut is the SAME eligible maximum; a purported separate earlier physical residual frontier is spurious.

## Acceptance gate

Create a standalone Lean module importing the merged E67 and E65 statements. Verify the original three formal endpoints, then add (4) residual support upward closure under monotone old-live masks and (5) equality of the two maxima when the residual set is nonempty. Audit both the weak one-way soundness and the stronger exact-mask hypothesis separately. Use a dedicated 3-name standard-only axiom audit with parser negative self-test and an independent full Lake build. Keep PR draft until exact-head green. Do not edit frozen black manuscript prose or promote global validation marks.