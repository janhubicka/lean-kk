# Track F — physical mixed-occupancy gluing from genuine disjoint markers

17 November 2026. English proof and hostile checks committed **before Lean**.
This composes the exact physical old-neighbourhood/raw-age support
locality (merged PRs #229/#237/#259) with the corrected mixed
singleton-occupancy transfer of merged PR #280. It is the
missing *finite constraint-transfer* API used by the olive
multi-daughter richness induction.

## Complete finite actual-graph data

Fix the ACTUAL directed ordinary graph table E, a chronological
old prefix [0,m), a later finite level n >= m, and parent sorts
P=Fin p, refined sorts D=Fin d. Let pi:D→P be an arbitrary
(non-injective) daughter-to-parent map.

Each parent a has a genuine finite old-neighbourhood
U_a⊆[0,m). Each refined daughter i has a fresh positive-marker set
V_i⊆[m,n). Assume **all V_i are pairwise disjoint**.

Set W_i = U_(pi i) ∪ V_i, the actual new neighbourhood of sort i.
For a support T of old parents define
b_old(T) = ell-1 - cap_E(∩_(a∈T) U_a).
For a support S of refined sorts define
b_new(S) = ell-1 - cap_E(∩_(i∈S) W_i).
All intersections are restricted to the appropriate old prefix,
as in the existing exact Lean common-neighbour definitions.

Choose a finite labelled clique vertex set B, each vertex
given a daughter label sort(x)∈D. Let N⊆D be the set of
NEW daughters. Assume:
1. Old parent feasibility: for every nonempty T⊆P, the number
   of vertices x∈B with pi(sort(x))∈T is at most b_old(T).
2. Every new daughter i∈N is occupied by at most ONE B vertex,
   and its new raw singleton bound b_new({i}) is at least 1.
3. Every UNCHANGED sort i∉N has no new positive marker:
   V_i=∅. Its original singleton bound need not be 1.

## Conclusion and English proof

Then for every nonempty refined support S⊆D, the number of
vertices x∈B with sort(x)∈S is at most b_new(S).

If |S|≥2, pairwise marker disjointness forces the fresh interval
to contribute no common old neighbour: every new common pool
on S is the original parent common pool on pi[S]. Hence
b_new(S)=b_old(pi[S]); the count on S is at most the parent
count on pi[S], which the old feasibility hypothesis bounds.

If S={i} and i∈N, use the assumed occupancy ≤1 and positive
new singleton bound. If S={i} and i∉N, V_i=∅, so the new
singleton raw bound is exactly the old bound on {pi(i)};
the daughter count is bounded by the count for that parent.
This proves all refined raw inequalities.

The *existing* graph-age canonicalizer preserves the set of
all normalized feasible labelled clique vectors. Therefore
the finite clique B remains admissible after canonicalization.
This last assertion requires its size to be below ell when
viewed as a normalized K_ell-free clique; the actual finite
K_ell-free application supplies that condition separately.

## Why this matters

The original PR #259 required every refined sort to have ≤1
selected vertex, incorrectly excluding legitimate B with several
vertices in an untouched lower-rank sort. PR #280 fixed the
pure counting statement. The present theorem derives its mixed
raw-equality AND untouched singleton-capacity hypotheses directly
from the concrete fresh marker sets and old prefix. This eliminates
an application gap in the finite combinatorial portion of the
olive richness induction, but not the induction's geometric
existence assumptions.

## Hostile checks

1. Marker sets must be pairwise disjoint even for two daughters of
   the same parent; otherwise a new common neighbour changes
   the mixed raw bound.
2. An unchanged sort must have V_i=∅; a positive fresh bit could
   lower its singleton capacity and exclude a formerly admissible B.
3. Newly created daughters need a POSITIVE singleton bound, not
   merely at-most-one selected vertex.
4. pi may identify distinct daughters; the image pi[S] may have
   smaller cardinality but remains nonempty for nonempty S.
5. The actual graph E may have arbitrary old edges; every capacity
   is a maximum directed clique, not cardinality of its pool.
6. The abstract feasible-vector theorem does not ensure that a
   particular induced Henson subcopy realizes B. Geometric source
   and target compatibility remain unverified.
7. Numerical canonical mixed ages can decrease as consequences of
   singleton constraints; only raw bounds and full clique feasibility
   are asserted.
8. This does not prove that the necessary rank-large daughter types
   exist simultaneously for ALL active source sorts.

## Acceptance

Formalize the one physical full-support feasibility implication
in Lean. Derive mixed equality from the exact disjoint markers,
derive unchanged singleton equality from V_i=∅, and invoke the
now-verified split/untouched occupancy lemma. Check its precise
transitive axioms at one exact head. No black manuscript text
or global BRD validation marker is to be changed.