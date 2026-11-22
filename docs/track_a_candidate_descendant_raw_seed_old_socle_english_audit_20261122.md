# Track A/C/G — complete RAW old-seed witness for ANY descendant Kpt candidate

22 November 2026. English FIRST; adversarial audit.

## Problem

The verified Track C source `Kk.TrackCRawOriginalOldSocle`
shows that equality of COMPLETE old dependent physical types
`A.partialTypeAt cut u = A.partialTypeAt cut v` plus one
genuine old seed x≤O_u crossing cut yields old lower Kpt
socle coverage for the ORIGINAL O_v.

The actual candidate source index in Track A/G contains many
more nodes than just original O_v: generated ancestors,
meets and E parameters. At a relevant cut, a candidate source
node z may merely satisfy z≤O_v, for a true ambient
original O_v, while z is NOT itself an original and may
not lie in the old source.

**Theorem.** Let A=finiteNumericH L k M genuinely avoid the
normalized forbidden family. Let R be an ACTUAL old
AlgorithmRun on seed X. Let z,x be genuine dependent Kpt
nodes, and u,v be physical original vertices in Fin M.
Assume:

* z≤A.kptOriginal(v) and x≤A.kptOriginal(u);
* x∈X (a TRUE old initial seed);
* cut<lev(z), cut<lev(x);
* A.partialTypeAt cut u.val = A.partialTypeAt cut v.val
  (the COMPLETE old raw record, not binary-L only).

Then z has a TRUE old lower Kpt-socle witness at cut,
namely x itself:

  KptActualOldSocleCoveredAt family X top R z cut.

### Proof in English

The already Lean-verified `kptBelowOriginal_ancestor_raw`
applied to z≤O_v gives
  val(ancestor_c z) = (c, A.partialTypeAt c v).
The same theorem applied to x≤O_u gives
  val(ancestor_c x) = (c, A.partialTypeAt c u).
The required equality of complete physical raw types
therefore yields equality of the two ancestor subtype
nodes by `Subtype.ext`. As x∈X, the verified general
seed inclusion
`SMTree.Envelope.subset_closure` places x in the
actual old pre-cut closure `closure(R.I(c+1),X)`.
Both nodes cross cut by assumption. Thus x is the
required complete OLD lower socle witness.

This does not rely on a Y AlgorithmRun, a source injection,
equality of upper L+/E crossing pairs, or an ordinary
graph age projection.

## Strong application-facing form

The previously verified `KptRawOldSeedMatchAt` predicate
(Track C) packages the existence of u, x∈X, x≤O_u,
crossing x and O_v, and complete raw type equality at c.

If z≤O_v and z crosses c, this predicate certifies the same
old-socle property for z. The additional O_v crossing
assumption in the predicate is implied by z≤O_v
and cut<lev(z), but keeping the existing predicate avoids
introducing a duplicate source API.

Consequently, in the new Track A/G maximal odd-boring
frontier, it will suffice to show for each candidate index
j with a nonempty odd old-boring live cut set:
  - choose an ambient original v whose O_v is above z_j;
  - at the SINGLE maximal such cut, establish
    KptRawOldSeedMatchAt(...,v,maxcut).

The new theorem then gives the maximal complete OLD
lower-socle witness required by the odd Bad source bound.
This is a finite physical raw-type certificate, but
the *existence* of those seed matches from a resolved
diary remains an open geometric problem.

## Adversarial checks

1. z can be an auxiliary parameter or meet node, not an
   original. The proof must not assume z=O_v.
2. The old x is an actual SEED in X, not merely a proposed
   candidate source or equal ordinary-L shadow.
3. Both z and x must STRICTLY cross the cut. Inclusion
   below an original alone does not imply that.
4. Complete old raw `partialTypeAt` equality is needed;
   one positive binary-L edge pattern is insufficient
   because auxiliary E and negative atoms are retained.
5. The original v need not be in the seed X; only x is.
6. The two physical originals O_u, O_v may differ, as in
   the previously validated Track C result.
7. Old pre-cut source closure is computed with the true
   old R.I(c+1), not an assumed new Y-run.
8. No new Run exists on Y by this argument.
9. The actual original-vertex types must be from the SAME
   finite H+ structure A and same numerical cut.
10. The physical carrier M is finite and u,v∈Fin M, so
    both original positions genuinely exist; no
    fictitious total-Nat vertex assumptions.
11. No restriction to odd cuts is needed in this lemma:
    it applies to ANY numeric source cut where hypotheses hold.
12. Equality of old complete Kpt ancestors does NOT by
    itself establish upper source pair equality unless
    the stage has extra zero-column hypotheses. The
    forthcoming odd frontier uses it only to exclude
    the missing lower socle branch.
13. For no suitable old seed x or matching raw type
    the lemma offers no conclusion. It does not
    eliminate real K4 q2 auxiliary exceptions.
14. Finite parameters, selected heights and diary
    features remain unresolved; no uniform Q or
    exact BRD bound is claimed.
15. Before merge, exact-head direct/full Lean build
    and named standard-only transitive axiom check
    are mandatory; manuscript black text is frozen.

## Lean targets

`Kk/TrackACandidateDescendantRawSocle.lean`:
- `finiteNumericH_candidate_below_original_old_socle_of_seed_raw_type_eq`;
- `finiteNumericH_candidate_below_original_old_socle_of_raw_seed_match`.

Import verified `Kk.TrackCRawSeedSafeRun` and reuse
existing `KptActualOldSocleCoveredAt`, not a duplicate
predicate. The next composition with the odd maximal
frontier must wait for PR #503 to pass and merge.
