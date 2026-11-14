# Track F — exact two-sort integer-clique capacity (English first)

**Standalone finite lemma** from the adversarial audit [TRACK_F_PAIR_PASSING_ENGLISH_AUDIT_20261114.md](https://github.com/janhubicka/Counting-big-Ramsey-degrees-of-K_k-free-graphs/blob/kk-track-f-deletion-restriction-20261114/TRACK_F_PAIR_PASSING_ENGLISH_AUDIT_20261114.md). The manuscript's word edge predicate will be compared with abstract passing bits only after the positive-initial-segment invariant is formally established.

## Precise two-sort result

Fix `ell ≥ 3` and the actual support type `IntegerGraphSupport 2 ell`, comprising exactly the three nonempty supports `{0}`, `{1}`, and `{0,1}`. Let B be any raw capacity function on those supports, **not** assumed to be an age. Assume only `B({0,1}) ≤ ell−1`, as is automatic for raw concrete word bounds.

Then the true finite normalized-clique canonical age at the full pair is

`G_B({0,1}) = min(B({0,1}), B({0}) + B({1}))`.

The proof uses **actual** normalized integer-clique vectors w of total weight ≤ell−1, not a surrogate interface.

## Proof with explicit realizing witness

Any B-feasible weight pair (u,v) satisfies `u≤B({0})`, `v≤B({1})`, `u+v≤B({0,1})`, and `u+v≤ell−1`. Therefore `u+v≤M=min(B({0,1}),B({0})+B({1}))`. This gives G_B(full)≤M.

Conversely choose `u=min(B({0}),M)`, `v=M-u`. Because M≤B({0})+B({1}), one has v≤B({1}); by construction u≤B({0}). Also u+v=M≤B({0,1})≤ell−1. Therefore the actual normalized `Fin ell` vector with weights u at 0 and v at 1 is B-feasible and attains mass M on the pair. Taking the genuine finite supremum gives G_B(full)≥M.

This formula does **not** use support monotonicity, but **raw pair capacity ≤ell−1 is essential**. Example: ell=4 and raw bounds B({0})=B({1})=3, B({0,1})=100 give RHS 6 although every normalized witness has total ≤3. The raw concrete word condition always gives pair capacity ≤ell−1, so the manuscript's intended application is safe.

## Next lemma before E versus X

For support-monotone B with all raw capacities ≤ell−1, one has G_B({i})=B({i}). Upper bound is canonicalization ≤raw. For the lower bound place weight B({i}) at coordinate i and zero at the other sort; the monotonic pair bound ensures feasibility. This permits replacing raw singleton capacities with actual canonical singleton ages in the two-sort formula.

Combining that theorem with the now-verified arbitrary injection `trackFCanonical_reindex_mono` (PR #139) gives for distinct sorts j,x in any finite concrete level:

`F({j,x}) = min(phi({j,x}),F({j})+F({x}))`.

Finally let j have singleton age 1, and let a be the largest positive letter on branch x, c the largest positive letter occurring at the same coordinate of j and x. If both positive letter sets are initial segments then the abstract bit test and concrete E both reduce to `a≥1 and c<a`. The initial-segment hypothesis is **not optional**; K4 one-letter words x=(1),j=(2) refute the equivalence on arbitrary histories.

## Formalization gate

This PR proves the exact two-sort capacity formula in `Kk/TrackFPairCapacity.lean`, with actual `IntegerCliqueWeights 2 ell`. Require targeted compilation and strict standard-only `#print axioms`; no changes to central Lean validation and no claim that this one result proves E↔X, the non-free splitting step, full diary equivalence or a new infinite lower bound.
