# Track E E68 — residual maximal-frontier reduction for genuine Kpt runs

**18 November 2026. English mathematical proof and adversarial audit, committed BEFORE Lean.**

## Motivation and exact scope

E63 builds one coherent old-final to new-final physical Kpt index for two genuine nested numerical-H+ runs. E64 says that at an old-boring cut, any genuinely NEW terminal or unmatched complete old/upper L+ crossing must have a NEW-LIVE index outside the image of OLD-LIVE indices. E65 distinguishes (a) new final index names from (b) old-final names newly active at the cut. E67 proves that for ONE fixed actual new Kpt node, complete old crossing coverage at its maximal eligible source cut implies coverage at every earlier eligible cut.

The missing elementary composition is to eliminate all OLD-LIVE image names **before** computing the E67 maximal frontier. Otherwise a maximal eligible cut may be harmless because the name is old-live there, even though there are smaller cuts at which the same name is newly active. That would make an unfiltered maximal test poorly targeted. The correct source-dependent filter is given below.

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

This equivalence is **stronger as a testing procedure** than E67 alone: an old-live maximal eligible cut never hides the need to test an earlier residual cut. The maximal residual cut may occur at a different source level from the maximal unrestricted eligible cut.

## Corollary E68.3 — the two genuine E65 residual kinds remain

If phi is additionally injective, each c in R_j satisfies precisely the E65 dichotomy:

* j is outside the image of ALL old FINAL names; or
* j is a matched old FINAL name whose old pre-cut live flag is false at c.

The second possibility must NOT be discarded as harmless. In particular an old-final node may have a long early activation interval (E66), so one residual maximum does not mean one interesting cut or one diary event.

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
20. No numerical-H+ diary realization, arbitrary-occurrence normalized orbit, global Ramsey upper bound or sharp BRD is claimed.

## Acceptance gate

Create a standalone Lean module importing the merged E67 and E65 statements. Verify the three formal endpoints: (1) old-live node self-witness; (2) exact residual-frontier maximal-cut equivalence; (3) E65 classification of the frontier under injectivity. Use a dedicated 3-name standard-only axiom audit with parser negative self-test and an independent full Lake build. Keep PR draft until exact-head green. Do not edit frozen black manuscript prose or promote global validation marks.