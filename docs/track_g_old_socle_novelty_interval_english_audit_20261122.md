# Track G — old-socle novelty intervals and the zero-stage exact-Bad cover

22 November 2026. English proof and hostile audit FIRST, before Lean.

## Setting

Fix one normalized Kpt forbidden family, one actual old AlgorithmRun R on seed set X with finite top t, and ANY candidate seed set Y in the SAME Kpt tree. No target AlgorithmRun on Y is required. At cut c<t define the genuine FULL candidate source

  C_Y(c) = closure(S,R.I(c+1),Y),

including all dependent E/negative L parameters and meets. The same OLD R-selected tails are used in both old and candidate closures.

## Lemma A — downward persistence of candidate source

For 0≤a≤b<t, C_Y(b)⊆C_Y(a). This follows from R.I_eq_final_tail_of_run, giving I(b+1)⊆I(a+1), and closure monotonicity with a fixed Y. It does NOT presuppose that Y has an AlgorithmRun, nor assert equal sources.

## Lemma B — downward persistence of old complete LOWER-socle coverage

Define OldSocleCovered(z,c) iff some w∈C_X(c) crosses c and shares the literal complete level-c Kpt ancestor with z, with lev(z)>c. If OldSocleCovered(z,b) and a≤b<t, then OldSocleCovered(z,a).

Proof: retain the same old witness w, which remains in C_X(a) by Lemma A applied to X. Both w,z reach b>a. Their equality of full Kpt ancestors at b restricts to equality at a by the already verified G294 `kpt_LevelTree_lower_ancestors_eq_of_higher_eq`. No ordinary L projection or invented auxiliary E records.

## Lemma C — one-node NO-old-socle novelty is order convex

Define CandidateSocleNovel(z,c) iff lev(z)>c, z∈C_Y(c), and ¬OldSocleCovered(z,c). For a≤b≤c<top:

  CandidateSocleNovel(z,a) ∧ CandidateSocleNovel(z,c)
      ⇒ CandidateSocleNovel(z,b).

Proof: z is live at c, so remains live at b by Lemma A. It reaches b since it reaches c. If it had an old lower-socle mate at b, Lemma B would give such a mate at a, contradicting novelty there. Note the upper novelty endpoint is needed only to establish candidate liveness/level; its no-socle negation is not otherwise used.

This identifies an INTERVAL of cut coordinates per literal candidate Kpt node, possibly empty. It bounds neither the LENGTH of that interval nor the number of candidate nodes; intersecting with genuinely boring or zero-column cuts can split its support.

## Theorem D — cover exact zero-column factor Bad cuts by structural events and these intervals

Specialize to the genuine finite numerical-H+ symmetric graph signature (db=1,du=0,dd=1), with K avoiding the normalized family, a finite original pool U, nested seeds X⊆Y in the ambient original-prefix pool, one actual old run R, and an independently EXACT finite full candidate source index `(node:Fin Q→Kpt,live)`, evaluated on the OLD R.I tails.

At any cut c that is in the merged G406 exact factor-Bad Finset and has the actual full zero ordinary graph-L column over every eligible true stage original, the verified G449 trichotomy supplies either:

(I1) a live candidate terminal at c;
(I2) a genuine same-component meet of two live candidate nodes at c;
(S) one live candidate node z crossing c without an old COMPLETE LOWER Kpt ancestor witness.

If I1 and I2 are separately excluded, exactness of the finite target index supplies j∈Fin Q representing z; thus CandidateSocleNovel(node j,c). Each fixed j's novelty support is the interval of Lemma C. Therefore the set of zero-column exact factor-Bad cuts without structural I1/I2 is covered by AT MOST Q node-specific INTERVAL CARRIERS (one per finite target name), with no assertion that the Bad set itself has at most Q connected components after intersecting with zero/bored cuts.

## Adversarial audit

1. The candidate sources C_Y(c) are computed using the OLD actual R.I(c+1); do not use a non-existent Y-run.
2. The old/source closure monotonicity relies on the actual final-tail invariant, not arbitrary per-cut source families.
3. The same literal Kpt ancestor at b forces equality at a, including auxiliary E and negative L. A matching ordinary-L reduct would not suffice.
4. The mate w must be LIVE in the genuine OLD full closure at the relevant stage; a final source node inactive at that cut is not enough.
5. The node z must be live in the candidate full closure and have level >c; merely sitting in the candidate final pool is insufficient.
6. At a≤b≤c, novelty at LOW a rules out old coverage at b; novelty at HIGH c supplies live/level b. Both are used.
7. A candidate node's novelty support is order-convex on the common raw source cut coordinates, but its intersection with the old-boring/zero-stage set can be disconnected.
8. Q is the finite cardinality of the particular physical candidate full Kpt name universe, not bounded by the diary. A bound Q on interval carriers does NOT imply a bound Q on bad cuts or their connected components.
9. No source-index injectivity is needed for witness extraction; duplicates only make the carrier cover redundant.
10. The G449 physical trichotomy is conditional on a TRUE zero ordinary-L column at all eligible original source names, not graph-age/selected-front equality.
11. Target terminal I1 and genuine same-component meet I2 must be excluded separately to isolate socle novelty.
12. True zero-stage I2 fork cannot be ignored merely because old interestingness is boring; new candidate source may introduce a fork.
13. K4 genuine auxiliary cuts 10 and 22 remain selected, not silently discarded as boring.
14. No cross-occurrence chronological cut-coordinate map or common labelled inverse-source orbit is constructed.
15. This does not establish the actual resolved diary has a uniform number of candidate Kpt names, nor prove a sharp BRD number.

## Acceptance

Lean theorem endpoints: candidate source monotone downward, old lower-socle cover monotone downward, per-node socle novelty order convex, and a zero-stage exact-factor-Bad witness corollary with I1/I2 excluded. Strict exact-head module compile and four qualified standard-only axiom reports with negative parser test; independent full repository build. Leave frozen black manuscript untouched. If a mathematical assumption in G449 does not match the proposed corollary, correct the English proof before adding axioms.
