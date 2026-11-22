# Track G — charge zero-column exact-Bad Kpt events to ORIGINAL socle thresholds

22 November 2026. English proof and adversarial audit BEFORE Lean.

## Goal

PR #469 identifies node-specific order-convex intervals of missing old COMPLETE lower Kpt socles and charges each zero-column exact factor-Bad cut without I1/I2 to one candidate node interval. The actual complete Kpt source index can be enormous (depending on all generated auxiliary E and meet nodes). Here we reduce the charging *carriers* from all candidate Kpt parameter nodes to the finite set of genuine H+ ORIGINAL vertices. This uses Track E E71's checked stage-original representation, not an invented graph-age projection.

## Lemma A — lower-socle matching transfers from an original to a represented node

Fix an actual old run R on X, cut c, candidate complete Kpt node z and an actual original Kpt node O with z≤O and lev(z)>c. Suppose O has an old-live COMPLETE lower-socle mate at c: some w in closure(S,R.I(c+1),X) crosses c and ancestor(O,c)=ancestor(w,c). Because z≤O and both reach c, ancestor(z,c)=ancestor(O,c), hence ancestor(z,c)=ancestor(w,c). So z itself has an old lower-socle mate.

Contrapositive: if z crosses c but has NO old lower-socle mate, then neither does any representing original O above z. This is a real Kpt ancestor equality including all dependent L+/E fields. Do not assume O is itself a live candidate or old-source closure node.

## Lemma B — one original's missing-old-socle cuts are an upper final segment

Fix an actual old run R, original O and top t. For 0≤a≤b<t with b<lev O, if O has no old lower-socle witness at a, it cannot acquire an old witness at b. Otherwise PR #469's lower-socle coverage monotonicity brings the witness at b DOWN to a, contradiction.

Therefore the set `{c<min(t,lev O): ¬OldSocleCovered(O,c)}` is UPWARD CLOSED within the finite raw cut domain and hence an interval, possibly empty. This is strictly stronger than mere order convexity. It is a set of source-coordinate cuts, not yet restricted to actual old-boring, zero-column or original-stage-live cuts.

## Theorem C — exact zero-stage Bad cuts without I1/I2 are charged to real originals

Work with the actual finite numerical-H+ symmetric graph Kpt signature (1,0,1), genuine X⊆Y in one ambient original-prefix pool U, old run R, and an exact full candidate finite target Kpt index (node/live) along R.I tails. Let c be an exact G406 factor-Bad cut. Assume its true full-stage ordinary graph L column is zero, and the candidate closure at c has neither a terminal (I1) nor a same-component meet (I2).

PR #469 supplies some LIVE candidate Kpt node z crossing c without an old COMPLETE lower Kpt socle. The verified E71 representation `finiteNumericH_stage_closure_represented_by_stage_originals` supplies an original v∈hStageOriginals(K,k,N,U,R.I(c+1)) with z≤O_v. By Lemma A, O_v also has NO old complete lower-socle witness at c, and reaches c. Hence

  ∃ v:Fin N, v∈hStageOriginals(K,k,N,U,R.I(c+1))
      ∧ c<lev(O_v) ∧ ¬OldSocleCovered(O_v,c).

Every such original has a single upper-final-segment missing-socle carrier by Lemma B. Thus zero-stage, no-I1/no-I2 exact Bad cuts can be charged to at most N ORIGINAL-coordinate upper-interval carriers, rather than Q potentially numerous auxiliary Kpt candidate names. The conclusion is a COVER, not an equality or a bound on actual Bad-cut count.

## Adversarial checks

1. The representing original v is obtained from the TRUE COMPLETE stage source closure on Y, not from selected-front ordinary L ages.
2. The original O_v need not itself be live in that source, and cannot be assumed to satisfy any selected I-level membership.
3. The physical z≤O_v relation is in the actual Kpt partial order, preserving ALL dependent E and negative L in ancestors.
4. Equality of ancestors at c follows from LevelTree.eq_ancestor_of_le, NOT an ordinary-L type projection.
5. Old lower-socle coverage must use an OLD LIVE crossing w at cut c, not a final source name that only activates later.
6. Missing lower-socle persists UPWARD below min(top,lev O) because old coverage persists DOWNWARD.
7. The stage-original condition `v∈hStageOriginals` varies with cut and need not be an upper interval; intersections with stage-active or zero/bored cuts can have many components.
8. Hence N ORIGINAL-carrier upper intervals is NOT an N bound on Bad-cut cardinality or components after filtering.
9. The actual finite numerical-H+ N can grow arbitrarily with the embedding; no diary-uniform N bound follows.
10. The target source index Q may be much larger than N; changing to original carriers meaningfully removes meet/parameter indexing from the witness accounting but does not solve uniformity.
11. I1 and I2 must be excluded independently; a zero graph column alone is insufficient unless additional verified physical zero-star hypotheses are available.
12. The G449 theorem's zero condition is over ALL eligible actual stage originals, not only the chosen v.
13. Genuine K4 selected auxiliary cuts 10 and 22 remain part of the raw scan.
14. Even after interval charging, a common labelled inverse-source orbit, chronological cut-coordinate map, corrected B3/relative continuation, unbounded resolved copy and sharp Kk-free BRDs remain OPEN.

## Lean plan

After PR #469's exact-head Lean check succeeds, import its source and Track E E71. Prove (A) original-lower-socle-cover transfer, (B) upward persistence of missing old socle, and (C) exact zero-column Bad without structural events has some genuine ORIGINAL representative with missing old socle. Direct module build and three exact named standard-only axiom reports with parser negative test, plus full integrated Lean CI. Keep frozen black manuscript unchanged and no green global upgrade.