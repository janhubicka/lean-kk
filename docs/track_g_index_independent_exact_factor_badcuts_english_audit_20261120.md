# Track G — enumeration-independent exact factor-Bad support and physical H+ application

20 November 2026. English first, adversarially audited before Lean. Depends on the exact finite Bad iff theorem in G406; do not claim it verified until its standalone Lean CI succeeds.

## The intrinsic one-cut predicate

Fix one actual RX on X and candidate target seeds Y, a numerical cut c, and let `C_Y(c)=closure(S,RX.I(c+1),Y)` be the COMPLETE dependent Kpt candidate source.

Define `PhysicallyOldFactorCompatible(c)` by three statements:

(T) no z∈C_Y(c) ends at c;
(M) no pair a,b∈C_Y(c) has the actual same-component meet at c;
(F) every genuine total MMap D with RX.F(c)=RX.F(c+1)∘D sends the lower-cut ancestor of EVERY crossing z∈C_Y(c) to its upper-cut ancestor.

Under the already verified G309 left cancellation and old-boringness, there is exactly one such D, namely RX's genuine old noninteresting-step factor. The predicate is a literal physical-node statement and therefore independent of finite names. It is not a consequence of equality of selected graph ages.

## Theorem A — exact finite index equivalence

For ANY finite node index `(node,live)` satisfying exactness of complete `C_Y(c)` at the cut c,

  KptIndexedOldFactorCompatibleAt(family,X,t,RX,node,live,c)
     iff PhysicallyOldFactorCompatible(c).

Proof: each indexed active terminal and each indexed active meet pair is a physical source terminal or meet pair by exactness. Every actual physical z∈C_Y(c) has some live j representing it; the total-map crossing equation is invariant under rewriting z=node(j) and proof irrelevance for ancestor level witnesses. Both implications are pointwise. The finite index need not be injective, and its cardinality may differ between representations.

## Theorem B — exact Bad support is INDEX-INDEPENDENT

If two different finite index/mask systems both exhaust the same complete target `C_Y(c)` at every old-range cut, then

  kptExactOldFactorBadCuts(node₁,live₁)
       = kptExactOldFactorBadCuts(node₂,live₂)

as actual Finsets of numerical cut coordinates (not just equivalent emptiness).

Proof: expand membership; the cut<top and old-boring checks do not involve the target index. The final failed-compatibility predicate is identical by Theorem A for each index. Finset extensionality yields equality.

This makes the exact factor-Bad set intrinsic to the actual old run and physical target source, unlike arbitrary choices of finite source labels. It is mathematically finite but does not imply a diary-uniform size bound.

## Theorem C — one-sided finite numerical-H+ closure gives exact test without target run

Given a finite genuine numerical-H+ pool, X⊆Y inside its ambient source, and one actual RX on X, the verified G378 `finiteNumericH_any_I_tails_uniform_Kpt_source_index` constructs a finite target source index and masks for the prescribed RX.I tails without constructing an AlgorithmRun on Y.

The genuine RX selected-level final-tail invariant supplies the tail-inclusion condition. Apply G406's exact factor-Bad theorem to this new target index to get:

  ∃ full target params, live with exact pre-cut representation
     AND (kptExactOldFactorBadCuts(...) = ∅
             iff ∃ RY with RY.I=RX.I and RY.F=RX.F).

This dispenses with *both* an assumed target run and an assumed target full-source enumeration in a single finite physical stage. The remaining unresolved input is the actual compatible old-factor geometry, now precisely localized in an intrinsic finite Bad set.

## Adversarial checks

1. Exactly ONE old genuine AlgorithmRun is an input; do not assume a run on Y.
2. F-factor conditions are equalities of TOTAL MMaps, not relations on selected graph-age shadows.
3. Every old-boring cut has a factor, and it is unique by injectivity; outside old-boring cuts the index/physical equivalence still holds but the total-factor quantifier may be vacuous.
4. The bad support filters only truly old-boring cuts; false positives at already interesting levels are excluded.
5. The 'physical' predicate has full Kpt source nodes, not merely paired old/upper L+/E spectra which can forget node identity.
6. Exact finite source indexing may have repeated names; injectivity is not needed for equivalence.
7. Terminal I1 and same-component meet I2 checks must be separate from the factor-crossing test.
8. An unrelated target source requires actual Kpt source inclusion X⊆Y for the G406 transport equivalence.
9. No one-level pullback E1, no assumption of no-I2, and no arbitrary prescribed source map is smuggled in.
10. The finite H+ index uses real original-prefix level bounds, not a diary-uniform source bound.
11. A classical noncomputable `Finset.filter` does not implement an executable infinite monoid search.
12. Distinct index cardinalities are permitted; no cutwise node bijection is required.
13. The candidate target pre-cut source is indexed along RX.I(c+1), not an unknown Y-run's I.
14. K4 auxiliary selected cuts 10 and 22 are still genuine and cannot be quietly removed.
15. Zero Bad proves synchronized existence of one Y-run, not equality of all possible target run F choices.
16. Even all-cut event-profile equality can forget actual node sets (verified G366); no labelled inverse source follows.
17. A zero finite Bad set on one physical H+ stage gives no uniform control as the stage size grows.
18. No chronological cut-coordinate reindexing for diary occurrences, B3 relative continuation, unbounded resolved copy, or sharp big Ramsey degree follows.

## Lean acceptance

After G406 passes and merges: import G406 and G378. Prove the one-cut indexed↔physical equivalence, exact Bad Finset equality for two exhaustive indices, and finite numerical-H+ source-indexed exact-Bad characterization. English audited first, direct qualified named standard-only axiom gate, strict parser self-test and independent full build. Keep manuscript black text frozen and global claims pending.