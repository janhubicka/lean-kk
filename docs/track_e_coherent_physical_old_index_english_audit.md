# Track E E62 — one coherent finite index embedding for all old physical cuts

**16 November 2026. English proof and hostile audit before Lean.**
This work is stacked on the exact-head-verified E60 PR #265 and reuses
its genuine cross-height physical closure inclusion theorem.

## Improvement over E60

E60 proves that for each old cut c and each live old finite index i,
there exists a live new finite index j representing the SAME
admissible Kpt node. Its j may depend on c, so that statement
alone is not a coherent identification of parameter names.

A stronger, still *one-sided* theorem is available if the two
indices exhaust the **final** physical closure, as guaranteed
for actual finite numerical-H+ AlgorithmRuns by the separately
checked exhaustive source-index theorem. This is useful for
literal participant-name transport across old cuts.

## E62.1 — existence of one index embedding

Fix a forbidden family and one admissible normalized Kpt tree.
Let X⊆Y, oldTop h≤newTop H, and actual AlgorithmRuns R on X and Q
on Y. Assume a real seed in X of level h. Let finite index maps
oldNode : Fin P→Kpt and newNode : Fin Q→Kpt satisfy:

1. oldNode is injective, and EVERY oldNode(i) belongs to
   the FULL final old closure ZR_final=closure_(R.I 0)(X);
2. newNode exhausts the FULL final new closure ZQ_final:
   z∈ZQ_final iff ∃j, newNode(j)=z;
3. at each c<h the old live mask is sound:
   oldLive(c,i)=true ⇒ oldNode(i)∈ZR(c);
4. at each c<h the new live mask is complete AND sound:
   newLive(c,j)=true iff newNode(j)∈ZQ(c).

First use checked cross-height selected-level monotonicity at i=0,
then monotonicity of closure in the selected parameter levels and
seed set, to prove **ZR_final ⊆ ZQ_final**.
For every old index i choose j such that
newNode(j)=oldNode(i). This choice is legitimate because of
the two final-closure premises.

Let φ(i)=that single chosen j. Then:

- for EVERY old i, newNode(φ(i))=oldNode(i);
- φ is injective because oldNode is injective: if φ(i)=φ(k)
  then oldNode(i)=newNode(φ(i))=newNode(φ(k))=oldNode(k);
- crucially, φ is a single function defined *before* selecting
  any cut c; for EVERY c<h and old-live i, E60's literal
  ZR(c)⊆ZQ(c) ensures the SAME node oldNode(i) lies in ZQ(c),
  so newLive(c,φ(i))=true;
- both raw dependent old/upper L+ ancestors of newNode(φ(i))
  at c are identical to those of oldNode(i), retaining auxiliary
  E, unary/diagonal and all positive/negative binary atoms.

This gives a coherent **all-cut old-index embedding**. It does not
assert surjectivity of φ, equality of the sizes P,Q, or that
no NEW-only physical source event occurs.

## E62.2 — canonical uniqueness for injective new enumeration

If newNode is also injective (as in the genuine exhaustive
finite-Kpt-source indexing theorem), any two functions
φ,ψ : Fin P→Fin Q with
newNode(φ(i))=oldNode(i)=newNode(ψ(i)) for every i
are EQUAL by injectivity of newNode. This makes the physical
old-to-new index embedding canonical relative to the two
actual final enumeration functions, not merely arbitrary
per-cut choices.

The *numerical indices* still depend on arbitrary finite
enumeration conventions. Only the corresponding physical-node
mapping is intrinsic.

## Hostile test checklist (20)

1. Need a genuine old top seed of level exactly h; a horizon marker
   alone does not force selected-level monotonicity across heights.
2. X⊆Y must be literal Kpt seed inclusion, not graph-age equality.
3. Both runs live in the same normalized Kpt tree.
4. The final physical closure uses R.I(0), not R.I(h).
5. The new final index is genuinely exhaustive; a selected-only
   or positive-upper type spectrum does NOT suffice.
6. Every old index names an actual old final-closure node;
   arbitrary ambient unused indices would invalidate the choice.
7. Index injectivity of oldNode is needed for φ injectivity.
8. Index injectivity of newNode is NOT needed for existence,
   but is needed for uniqueness.
9. φ is chosen once for all cuts; never choose a fresh j(c,i).
10. Old active soundness is enough; no false assumption of
    old/new per-cut index sizes being equal is needed.
11. New live mask must be complete at each old cut.
12. Source coordinates c are genuine Kpt cut levels, not numerical
    target-generation gap ordinals from unrelated structures.
13. The full closure includes meet and positive parameter nodes,
    not merely the original Kpt seed leaves.
14. Old-to-new physical retention does not imply the reverse
    NEW-to-OLD off-plan no-novelty tests.
15. Complete old and upper dependent L+ types are preserved because
    the full actual Kpt node is identical, not just its L reduct.
16. I2 forks can produce multiple new crossing pairs not present
    in the old source; nothing rules them out.
17. E55 intrinsic bad-cut support can grow even when this φ exists.
18. A coherent index injection for ONE nested pair of runs does
    not identify parameter names across different resolved-diary
    occurrences lacking literal seed inclusion/common source tree.
19. Selected finite G+ vertices are a separate sort: their
    distinguished type-vertex assignments are not determined by
    equality of ordinary socle codes.
20. No uniform diary size bound, common labelled monoid orbit,
    unbounded resolved-H+ recursion, or BRD conclusion follows.

## Next genuine application

Use E61's constructed exhaustive index for a true old/new
finite numerical-H+ pair (both with correct forbidden-family
avoidance and actual old seed). This should supply the final
exhaustivity, injectivity and live-mask premises without
postulating a new finite-index encoding.

Then compare the residual NEW-only physical nodes and the
full same-node crossing relation; this is where an actual
diary-derived microevent schedule and E/age constraints are
still required. The present theorem does not pretend to
discharge that crucial reverse inclusion.

## Lean validation plan

Implement as an independent module importing
\`Kk.TrackEOldPhysicalIndexRetention\`. Explicitly compile it
with a strict two-name transitive-axiom report and independent
ordinary full build. No new manuscript mark until both pass.
Black manuscript mathematics stays frozen.
